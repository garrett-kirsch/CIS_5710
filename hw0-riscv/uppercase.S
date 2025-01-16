        .section .data
input_string:   .asciz "Hello world!~~~  pasdgoaihGPIOSDHOIHknaeogi][]{}||\!@#$%^&*()_-+=~`     "

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        # Your code here!

        loop:

                # iterate over chars and check if each is lowercase
                # if yes, add -32 to the char
                # move on to the next char

                # t0 = current char
                lb t0, 0(a0)

                # check if t0 is null -> if yes, terminate
                beq t0, x0, end_program

                # check if t0 is lowercase -> if no, skip to not_lowercase
                addi t1, zero, 97
                blt t0, t1, not_lowercase
                addi t1, zero, 123
                bge t0, t1, not_lowercase

                # subtract 32 from t0 and store it in a0
                addi t0, t0, -32
                sb t0, 0(a0)

                not_lowercase: 
                
                # increment a0 by 1
                addi a0, a0, 1

                j loop
        
end_program:
        # jump here when you're done
        j end_program

