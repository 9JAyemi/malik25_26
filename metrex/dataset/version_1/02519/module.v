module my_dff ( 
    input clk, 
    input d, 
    output reg q 
);

always @(posedge clk) begin
    q <= d;
end

endmodule

module shift_register_adder ( 
    input clk, 
    input [3:0] adder_input, 
    input d, 
    output reg [6:0] sum 
);

    reg [3:0] shift_reg;
    reg [4:0] shifted_input;
    reg [4:0] adder_output;
    wire q;

    my_dff dff_inst (
        .clk(clk),
        .d(d),
        .q(q)
    );

    always @* begin
        shifted_input = {shift_reg[2], shift_reg[1], shift_reg[0], 1'b0};
        adder_output = adder_input + shifted_input;
        shift_reg <= {shifted_input[3:1], d};
    end

    always @* begin
        sum = {adder_output, shift_reg};
    end

endmodule