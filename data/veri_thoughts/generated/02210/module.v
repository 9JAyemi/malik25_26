
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] sum,
    output reg carry_out
);

    reg [3:0] carry;
    
    always @(*) begin
        {carry_out, sum} = A + B + carry;
    end
    
    always @(posedge carry_out) begin
        carry <= carry_out;
    end
    
endmodule