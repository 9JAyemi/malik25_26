module MUXF7 (O, I0, I1, I2, I3, I4, I5, I6, S);

    output O;
    input I0, I1, I2, I3, I4, I5, I6, S;

    reg O_out;

    always @(I0 or I1 or I2 or I3 or I4 or I5 or I6 or S) 
    begin
        case(S)
            3'b000: O_out = I0;
            3'b001: O_out = I1;
            3'b010: O_out = I2;
            3'b011: O_out = I3;
            3'b100: O_out = I4;
            3'b101: O_out = I5;
            3'b110: O_out = I6;
            default: O_out = 1'b0; // This is the default value in case S is not a valid input
        endcase
    end

    assign O = O_out;

endmodule