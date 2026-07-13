
module MUX_2_1 (
    input wire I0,
    input wire I1,
    input wire S,
    output reg O
);

    parameter CLK_SEL_TYPE = "SYNC";

    always @ (S) begin
        case (S)
            1'b0: O = I0;
            1'b1: O = I1;
        endcase
    end

endmodule
