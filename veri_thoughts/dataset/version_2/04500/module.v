
module input_output(
    input        clk,
    input  [6:0] a,
    input        a_msb,              
    output [14:0] b,              
    output       b_msb            
);

    wire c;

    reg [15:0] b_reg = 0;      

    assign c = a_msb & b_reg[0];

    always @(posedge clk) begin
        b_reg <= b_reg + {a_msb ? {8'd255, a} : {8'd0, a}};
    end

    assign b_msb = b_reg[15];
    assign b = {b_reg[14:0], c};

endmodule