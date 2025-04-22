`timescale 1ns / 1ns

`define ADDR_WIDTH 32
`define DATA_WIDTH 32

interface axi_if #(
      parameter int ADDR_WIDTH = 32
    , parameter int DATA_WIDTH = 32
);
  logic                      ARREADY;
  logic                      ARVALID;
  logic [    ADDR_WIDTH-1:0] ARADDR;
  logic [               2:0] ARPROT;

  logic                      RREADY;
  logic                      RVALID;
  logic [    DATA_WIDTH-1:0] RDATA;
  logic [               1:0] RRESP;

  logic                      AWREADY;
  logic                      AWVALID;
  logic [    ADDR_WIDTH-1:0] AWADDR;
  logic [               2:0] AWPROT;

  logic                      WREADY;
  logic                      WVALID;
  logic [    DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;

  logic                      BREADY;
  logic                      BVALID;
  logic [               1:0] BRESP;

  modport manager(
      input ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP,
      output ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY
  );
  modport subord(
      input ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY,
      output ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP
  );
endinterface

// [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
`define RESP_OK 2'b00
`define RESP_SUBORDINATE_ERROR 2'b10
`define RESP_DECODE_ERROR 2'b11

/** This is a simple memory that uses the AXI-Lite interface. */
module AxilMemory #(
    parameter int NUM_WORDS = 1024
) (
    input wire ACLK,
    input wire ARESETn,
    axi_if.subord port_ro,
    axi_if.subord port_rw
);
  localparam bit True = 1'b1;
  localparam bit False = 1'b0;
  localparam int AddrLsb = 2;  // since memory elements are 4B
  localparam int AddrMsb = $clog2(NUM_WORDS) + AddrLsb - 1;

  logic [31:0] mem_array[NUM_WORDS];
  logic [31:0] ro_araddr;
  logic ro_araddr_valid;

  initial begin
`ifdef SYNTHESIS
    $readmemh("mem_initial_contents.hex", mem_array);
`endif
  end

  assign port_ro.RRESP = `RESP_OK;
  assign port_ro.BRESP = `RESP_OK;
  assign port_rw.RRESP = `RESP_OK;
  assign port_rw.BRESP = `RESP_OK;

  always_ff @(posedge ACLK) begin
    if (!ARESETn) begin
      ro_araddr <= 0;
      ro_araddr_valid <= False;

      port_ro.ARREADY <= True;
      port_ro.AWREADY <= False;
      port_ro.WREADY  <= False;
      port_ro.RVALID <= False;
      port_ro.RDATA <= 0;

      port_rw.ARREADY <= True;
      port_rw.AWREADY <= True;
      port_rw.WREADY  <= True;
      port_rw.RVALID <= False;
      port_rw.RDATA <= 0;
    end else begin

      // port_ro is read-only

      if (ro_araddr_valid) begin
        // there is a buffered read request
        if (port_ro.RREADY) begin
          // manager accepted our response, we generate next response
          port_ro.RVALID <= True;
          port_ro.RDATA  <= mem_array[ro_araddr[AddrMsb:AddrLsb]];
          ro_araddr <= 0;
          ro_araddr_valid <= False;
          port_ro.ARREADY <= True;
        end
      end else if (port_ro.ARVALID && port_ro.ARREADY) begin
        // we have accepted a read request
        if (port_ro.RVALID && !port_ro.RREADY) begin
          // We have sent a response but manager has not accepted it. Buffer the new read request.
          ro_araddr <= port_ro.ARADDR;
          ro_araddr_valid <= True;
          port_ro.ARREADY <= False;
        end else begin
          // We have sent a response and manager has accepted it. Or, we were not already sending a response.
          // Either way, send a response to the request we just accepted.
          port_ro.RVALID <= True;
          port_ro.RDATA  <= mem_array[port_ro.ARADDR[AddrMsb:AddrLsb]];
        end
      end else if (port_ro.RVALID && port_ro.RREADY) begin
        // No incoming request. We have sent a response and manager has accepted it
        port_ro.RVALID <= False;
        port_ro.RDATA  <= 0;
        port_ro.ARREADY <= True;
      end

      // port_rw is read-write

      // NB: we take a shortcut on port_rw because the manager will always be RREADY/BREADY
      // as 1) the datapath never stalls in the W stage and 2) the cache is always ready
      if (port_rw.ARVALID && port_rw.ARREADY) begin
        port_rw.RVALID <= True;
        port_rw.RDATA  <= mem_array[port_rw.ARADDR[AddrMsb:AddrLsb]];
      end else if (port_rw.RVALID) begin
        port_rw.RVALID <= False;
        port_rw.RDATA  <= 0;
      end

      if (port_rw.AWVALID && port_rw.AWREADY && port_rw.WVALID && port_rw.WREADY) begin
        if (port_rw.WSTRB[0]) begin
          mem_array[port_rw.AWADDR[AddrMsb:AddrLsb]][7:0] <= port_rw.WDATA[7:0];
        end
        if (port_rw.WSTRB[1]) begin
          mem_array[port_rw.AWADDR[AddrMsb:AddrLsb]][15:8] <= port_rw.WDATA[15:8];
        end
        if (port_rw.WSTRB[2]) begin
          mem_array[port_rw.AWADDR[AddrMsb:AddrLsb]][23:16] <= port_rw.WDATA[23:16];
        end
        if (port_rw.WSTRB[3]) begin
          mem_array[port_rw.AWADDR[AddrMsb:AddrLsb]][31:24] <= port_rw.WDATA[31:24];
        end
        port_rw.BVALID <= True;
      end else if (port_rw.BVALID) begin
        port_rw.BVALID <= False;
      end
    end
  end

endmodule

// States for cache state machine. You can change these if you want.
typedef enum {
  // cache can respond to an incoming request
  CACHE_AVAILABLE = 0,
  // cache miss, waiting for fill from memory
  CACHE_AWAIT_FILL_RESPONSE = 1,
  // cache miss, waiting for writeback to memory
  CACHE_AWAIT_WRITEBACK_RESPONSE = 2,
  // cache waiting for manager to accept response
  CACHE_AWAIT_MANAGER_READY = 3
} cache_state_t;

module AxilCache #(
    /** size of each cache block, in bits */
    parameter int BLOCK_SIZE_BITS = 32,
    /** number of blocks in each way of the cache */
    parameter int NUM_SETS = 4
) (
    input wire ACLK,
    input wire ARESETn,
    axi_if.subord  proc,
    axi_if.manager mem
);

  // TODO: calculate these
  localparam int ADDR_WIDTH = 32; // Assuming a 32-bit address space
  localparam int BlockOffsetBits = 2;
  localparam int IndexBits = $clog2(NUM_SETS);
  localparam int TagBits = ADDR_WIDTH - BlockOffsetBits - IndexBits;

  localparam bit True = 1'b1;
  localparam bit False = 1'b0;

  // cache state
  cache_state_t current_state;
  // main cache structures: do not rename as tests reference these names
  logic [BLOCK_SIZE_BITS-1:0] data[NUM_SETS];
  logic [TagBits-1:0] tag[NUM_SETS];
  logic [0:0] valid[NUM_SETS];
  logic [0:0] dirty[NUM_SETS];

  // initialize cache state to all zeroes
  genvar seti;
  for (seti = 0; seti < NUM_SETS; seti = seti + 1) begin : gen_cache_init
    initial begin
      valid[seti] = '0;
      dirty[seti] = '0;
      data[seti] = 0;
      tag[seti] = 0;
    end
  end

  always_comb begin
    // addresses should always be 4B-aligned
    assert (!proc.ARVALID || proc.ARADDR[1:0] == 2'b00);
    assert (proc.ARPROT == 3'd0);
    assert (!proc.AWVALID || proc.AWADDR[1:0] == 2'b00);
    assert (proc.AWPROT == 3'd0);
    // cache is single-ported
    assert (!(proc.ARVALID && (proc.AWVALID || proc.WVALID)));
  end
  // the cache never raises any errors
  assign proc.RRESP = `RESP_OK;
  assign proc.BRESP = `RESP_OK;

  // TODO: the rest of your changes will go below
  // processor outputs: ARREADY, RVALID, RDATA, AWREADY, WREADY, BVALID
  // mem outputs: ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY

  logic proc_AR_ready;
  logic proc_R_valid;
  logic [31:0] proc_R_data;
  logic proc_AW_ready;
  logic proc_W_ready;
  logic proc_B_valid;

  logic mem_AR_valid;
  logic [31:0] mem_AR_addr;
  logic mem_R_ready;
  logic mem_AW_valid;
  logic [31:0] mem_AW_addr;
  logic mem_W_valid;
  logic [31:0] mem_W_data;
  logic [3:0] mem_W_strb;
  logic mem_B_ready;

  logic write_hit;
  logic [IndexBits-1:0] write_index;
  logic [31:0] write_data;
  logic [3:0] write_strb;

  logic [IndexBits-1:0] index;
  logic [TagBits-1:0] tag_in;

  // get index and tag_index from the address 
  assign index = proc.ARVALID ? proc.ARADDR[BlockOffsetBits +: IndexBits] :
                                proc.AWADDR[BlockOffsetBits +: IndexBits];
  assign tag_in = proc.ARVALID ? proc.ARADDR[BlockOffsetBits + IndexBits +: TagBits] :
                                 proc.AWADDR[BlockOffsetBits + IndexBits +: TagBits];


  // Default values for outputs
  always_comb begin
    proc_AR_ready = False;
    proc_R_valid = False;
    proc_R_data = 0;
    proc_AW_ready = False;
    proc_W_ready = False;
    proc_B_valid = False;

    mem_AR_valid = False;
    mem_AR_addr = 0;
    mem_R_ready = False;
    mem_AW_valid = False;
    mem_AW_addr = 0;
    mem_W_valid = False;
    mem_W_data = 0;
    mem_W_strb = 0;
    mem_B_ready = False;

    next_state = CACHE_AVAILABLE;

    if (!ARESETn) begin // NB: reset when ARESETn == 0

      // Assign processor outputs
      proc_AR_ready = True;
      proc_AW_ready = True;
      proc_W_ready = True;
      
      // Assign memory outputs
      mem_R_ready = True;
      mem_B_ready = True;
      
      
    end else begin
      case (current_state)
        CACHE_AVAILABLE: begin
          // Extract address components
          proc_AR_ready = True;
          proc_AW_ready = True;
          proc_W_ready = True;

          if (proc.ARVALID) begin         

            if (valid[index] && tag[index] == tag_in) begin
              // Read Hit
              proc_R_valid = True;
              proc_R_data = data[index];
              if (proc.RREADY) begin
                next_state = CACHE_AVAILABLE;
              end else begin
                next_state = CACHE_AWAIT_MANAGER_READY;
              end
            end else begin
              // Read Miss: fetch from memory
              mem_AR_valid = True;
              mem_AR_addr = proc.ARADDR;
              if (mem.ARREADY) begin
                next_state = CACHE_AWAIT_FILL_RESPONSE;
              end else begin
                next_state = CACHE_AVAILABLE;
              end
            end

          end else if (proc.AWVALID && proc.WVALID) begin


            if (valid[index] && tag[index] == tag_in) begin
              // Write Hit
              // Apply WSTRB (byte enables)
              write_hit = True;
              write_index = index;
              write_data = proc.WDATA;
              write_strb = proc.WSTRB;

              dirty[index] = True;

              // Send write response to processor
              proc_B_valid = True;
              if (proc.BREADY) begin
                next_state = CACHE_AVAILABLE;
              end else begin
                next_state = CACHE_AWAIT_MANAGER_READY;
              end
            end else begin
              // Write Miss: write directly to memory
              mem_AW_valid = True;
              mem_AW_addr = proc.AWADDR;
              mem_W_valid = True;
              mem_W_data = proc.WDATA;
              mem_W_strb = proc.WSTRB;

              if (mem.AWREADY && mem.WREADY) begin
                next_state = CACHE_AWAIT_WRITEBACK_RESPONSE;
              end else begin
                next_state = CACHE_AVAILABLE;
              end
            end

          end else begin
            next_state = CACHE_AVAILABLE;
          end
        end


        CACHE_AWAIT_FILL_RESPONSE: begin
          
          mem_R_ready = True; // Tell memory we are ready for data
          if (mem.RVALID) begin
            proc_R_valid = True;        // Tell processor we have data
            proc_R_data = mem.RDATA;    // Forward data from memory to processor
            if (proc.RREADY) begin
              next_state = CACHE_AVAILABLE;  // Done with this transaction
            end else begin
              next_state = CACHE_AWAIT_MANAGER_READY; // Wait until processor takes data
            end
          end else begin
            next_state = CACHE_AWAIT_FILL_RESPONSE; // Stay here until mem responds
          end
        end


        CACHE_AWAIT_WRITEBACK_RESPONSE: begin
          mem_B_ready = True; // Tell memory we're ready for write response
          if (mem.BVALID) begin
            proc_B_valid = True; // Inform processor of write completion
            if (proc.BREADY) begin
              next_state = CACHE_AVAILABLE; // Done
            end else begin
              next_state = CACHE_AWAIT_MANAGER_READY; // Wait until processor accepts response
            end
          end else begin
            next_state = CACHE_AWAIT_WRITEBACK_RESPONSE; // Still waiting
          end
        end

        // end

        CACHE_AWAIT_MANAGER_READY: begin
          if ((proc.RVALID && proc.RREADY) || (proc.BVALID && proc.BREADY)) begin
            next_state = CACHE_AVAILABLE;
          end else begin
            next_state = CACHE_AWAIT_MANAGER_READY;
          end
        end


        default: begin
          next_state = CACHE_AVAILABLE;
        end
      endcase
    end
  end



  // Determine cache state
  cache_state_t next_state;

  // always_comb begin
  //   if (!ARESETn) begin // NB: reset when ARESETn == 0
  //     next_state = CACHE_AVAILABLE;
  //   end
  // end


  always_ff @(posedge ACLK) begin
    
    current_state <= next_state; // set next state

    // Assign processor outputs
    proc.ARREADY <= proc_AR_ready;
    proc.RVALID <= proc_R_valid;
    proc.RDATA <= proc_R_data;
    proc.AWREADY <= proc_AW_ready;
    proc.WREADY <= proc_W_ready;
    proc.BVALID <= proc_B_valid;

    // Assign memory outputs
    mem.ARVALID <= mem_AR_valid;
    mem.ARADDR <= mem_AR_addr;
    mem.RREADY <= mem_R_ready;
    mem.AWVALID <= mem_AW_valid;
    mem.AWADDR <= mem_AW_addr;
    mem.WVALID <= mem_W_valid;
    mem.WDATA <= mem_W_data;
    mem.WSTRB <= mem_W_strb;
    mem.BREADY <= mem_B_ready;

    if (write_hit) begin
      if (write_strb[0]) data[write_index][7:0]   <= write_data[7:0];
      if (write_strb[1]) data[write_index][15:8]  <= write_data[15:8];
      if (write_strb[2]) data[write_index][23:16] <= write_data[23:16];
      if (write_strb[3]) data[write_index][31:24] <= write_data[31:24];
      dirty[write_index] <= True;
    end
    

  end


endmodule // AxilCache

`ifndef SYNTHESIS
/** This is used for testing AxilCache in simulation. Since Verilator doesn't allow
SV interfaces in a top-level module, we wrap the interfaces with plain wires. */
module AxilCacheTester #(
    // these parameters are for the AXIL interface
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    // these parameters are for the cache
    parameter int BLOCK_SIZE_BITS = 32,
    parameter int NUM_SETS = 4
) (
    input wire ACLK,
    input wire ARESETn,

    input  wire                       CACHE_ARVALID,
    output logic                      CACHE_ARREADY,
    input  wire  [    ADDR_WIDTH-1:0] CACHE_ARADDR,
    input  wire  [               2:0] CACHE_ARPROT,
    output logic                      CACHE_RVALID,
    input  wire                       CACHE_RREADY,
    output logic [    ADDR_WIDTH-1:0] CACHE_RDATA,
    output logic [               1:0] CACHE_RRESP,
    input  wire                       CACHE_AWVALID,
    output logic                      CACHE_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] CACHE_AWADDR,
    input  wire  [               2:0] CACHE_AWPROT,
    input  wire                       CACHE_WVALID,
    output logic                      CACHE_WREADY,
    input  wire  [    DATA_WIDTH-1:0] CACHE_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] CACHE_WSTRB,
    output logic                      CACHE_BVALID,
    input  wire                       CACHE_BREADY,
    output logic [               1:0] CACHE_BRESP,

    output wire                       MEM_ARVALID,
    input  logic                      MEM_ARREADY,
    output wire  [    ADDR_WIDTH-1:0] MEM_ARADDR,
    output wire  [               2:0] MEM_ARPROT,
    input  logic                      MEM_RVALID,
    output wire                       MEM_RREADY,
    input  logic [    ADDR_WIDTH-1:0] MEM_RDATA,
    input  logic [               1:0] MEM_RRESP,
    output wire                       MEM_AWVALID,
    input  logic                      MEM_AWREADY,
    output wire  [    ADDR_WIDTH-1:0] MEM_AWADDR,
    output wire  [               2:0] MEM_AWPROT,
    output wire                       MEM_WVALID,
    input  logic                      MEM_WREADY,
    output wire  [    DATA_WIDTH-1:0] MEM_WDATA,
    output wire  [(DATA_WIDTH/8)-1:0] MEM_WSTRB,
    input  logic                      MEM_BVALID,
    output wire                       MEM_BREADY,
    input  logic [               1:0] MEM_BRESP
);

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) cache_axi ();
  assign cache_axi.manager.ARVALID = CACHE_ARVALID;
  assign CACHE_ARREADY = cache_axi.manager.ARREADY;
  assign cache_axi.manager.ARADDR = CACHE_ARADDR;
  assign cache_axi.manager.ARPROT = CACHE_ARPROT;
  assign CACHE_RVALID = cache_axi.manager.RVALID;
  assign cache_axi.manager.RREADY = CACHE_RREADY;
  assign CACHE_RRESP = cache_axi.manager.RRESP;
  assign CACHE_RDATA = cache_axi.manager.RDATA;
  assign cache_axi.manager.AWVALID = CACHE_AWVALID;
  assign CACHE_AWREADY = cache_axi.manager.AWREADY;
  assign cache_axi.manager.AWADDR = CACHE_AWADDR;
  assign cache_axi.manager.AWPROT = CACHE_AWPROT;
  assign cache_axi.manager.WVALID = CACHE_WVALID;
  assign CACHE_WREADY = cache_axi.manager.WREADY;
  assign cache_axi.manager.WDATA = CACHE_WDATA;
  assign cache_axi.manager.WSTRB = CACHE_WSTRB;
  assign CACHE_BVALID = cache_axi.manager.BVALID;
  assign cache_axi.manager.BREADY = CACHE_BREADY;
  assign CACHE_BRESP = cache_axi.manager.BRESP;

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) mem_axi ();
   assign MEM_ARVALID = mem_axi.subord.ARVALID;
   assign mem_axi.subord.ARREADY = MEM_ARREADY;
   assign MEM_ARADDR = mem_axi.subord.ARADDR;
   assign MEM_ARPROT = mem_axi.subord.ARPROT;
   assign mem_axi.subord.RVALID = MEM_RVALID;
   assign MEM_RREADY = mem_axi.subord.RREADY;
   assign mem_axi.subord.RRESP = MEM_RRESP;
   assign mem_axi.subord.RDATA = MEM_RDATA;
   assign MEM_AWVALID = mem_axi.subord.AWVALID;
   assign mem_axi.subord.AWREADY = MEM_AWREADY;
   assign MEM_AWADDR = mem_axi.subord.AWADDR;
   assign MEM_AWPROT = mem_axi.subord.AWPROT;
   assign MEM_WVALID = mem_axi.subord.WVALID;
   assign mem_axi.subord.WREADY = MEM_WREADY;
   assign MEM_WDATA = mem_axi.subord.WDATA;
   assign MEM_WSTRB = mem_axi.subord.WSTRB;
   assign mem_axi.subord.BVALID = MEM_BVALID;
   assign MEM_BREADY = mem_axi.subord.BREADY;
   assign mem_axi.subord.BRESP = MEM_BRESP;

  AxilCache #(
    .BLOCK_SIZE_BITS(BLOCK_SIZE_BITS),
    .NUM_SETS(NUM_SETS)
  ) cache (
      .ACLK(ACLK),
      .ARESETn(ARESETn),
      .proc(cache_axi.subord),
      .mem(mem_axi.manager)
  );
endmodule // AxilCacheTester
`endif
