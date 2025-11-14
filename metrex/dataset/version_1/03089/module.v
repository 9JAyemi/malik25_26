
module top_module (
    input clk,
    input reset,
    input [3:0] A,
    input [3:0] B,
    input [31:0] data_in,
    input [4:0] shift_amt,
    input select, // Select input to choose between addition and shifting
    output [31:0] result
);

    wire [3:0] adder_out;
    wire [31:0] shifted_out;
    wire mode_select;

    // Instantiate the ripple carry adder module
    ripple_carry_adder adder_inst (
        .clk(clk),
        .reset(reset),
        .A(A),
        .B(B),
        .sum(adder_out)
    );

    // Instantiate the barrel shifter module
    barrel_shifter shifter_inst (
        .data_in(data_in), // Fixed the port width mismatch
        .shift_amt(shift_amt),
        .shifted_out(shifted_out)
    );

    // Control logic to select between addition and shifting modes
    assign mode_select = select;

    // Output the result based on the selected mode
    assign result = (mode_select == 0) ? adder_out : shifted_out;

endmodule

module ripple_carry_adder (
    input clk,
    input reset,
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] sum
);

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            sum <= 4'b0;
        end else begin
            sum <= A + B;
        end
    end

endmodule

module barrel_shifter (
    input [31:0] data_in,
    input [4:0] shift_amt,
    output [31:0] shifted_out
);

    assign shifted_out = (shift_amt[4]) ? {32{data_in[31]}} :
                        (shift_amt[3]) ? {data_in[31], data_in[31:1]} :
                        (shift_amt[2]) ? {data_in[31:2], data_in[1:0]} :
                        (shift_amt[1]) ? {data_in[31:3], data_in[2:0]} :
                        {data_in[31:4], data_in[3:0]};

endmodule
