module add_sub_shift (
    input [15:0] in0,
    input [15:0] in1,
    input ctrl,
    input signed [3:0] SHIFT,
    input RESET,
    input clk, // Added missing clock input
    output reg [15:0] q
);

    wire [15:0] add_sub_out;
    wire [15:0] shift_out;
    
    add_sub_16bit add_sub_inst (
        .in0(in0),
        .in1(in1),
        .ctrl(ctrl),
        .out(add_sub_out)
    );
    
    barrel_shifter_4bit shift_inst (
        .in(add_sub_out),
        .shift(SHIFT),
        .out(shift_out)
    );
    
    always @(posedge clk or posedge RESET) begin // Changed sensitivity list to include clk and RESET
        if (RESET) begin
            q <= 0;
        end else begin
            q <= shift_out;
        end
    end
    
endmodule

module add_sub_16bit (
    input [15:0] in0,
    input [15:0] in1,
    input ctrl,
    output reg [15:0] out
);

    always @(*) begin
        if (ctrl) begin
            out = in0 + in1;
        end else begin
            out = in0 - in1;
        end
    end
    
endmodule

module barrel_shifter_4bit (
    input [15:0] in,
    input signed [3:0] shift,
    output reg [15:0] out
);

    always @(*) begin
        out = in << shift;
    end
    
endmodule