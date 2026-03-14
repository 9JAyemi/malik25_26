
module alu_slice_LA(a, b, c, less, sel, out, p, g);

    input a, b, c, less;
    input [2:0] sel;

    output out;
    reg out;
    output reg p, g;
    wire sum, cout, ANDresult, ORresult, b_inv, p1, g1;
    reg less_reg;

    assign  b_inv = sel[2] ^ b;
    assign  ANDresult = a & b;
    assign  ORresult = a | b;
   
    fulladder f1(a, b_inv, c, sum, p1, g1);

    always @(a or b or c or less or sel)
    begin
        case(sel[1:0])
            2'b00: out = ANDresult;
            2'b01: out = ORresult;
            2'b10: begin
                out = sum;
                p = p1;
                g = g1;
            end
            2'b11: begin
                if (a < b) begin
                    out = 1;
                    less_reg = 1;
                end else begin
                    out = 0;
                    less_reg = 0;
                end
            end
        endcase
    end

    assign less = less_reg;
   
endmodule
module fulladder(a, b, ci, s, p, g);
    input a, b, ci;
    output s, p, g;

    assign s = a ^ b ^ ci;
    assign p = (a & b) | (a & ci) | (b & ci);
    assign g = (a & b) | (b & ci);
endmodule