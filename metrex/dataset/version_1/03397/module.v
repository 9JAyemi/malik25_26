
module top_module (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out,
    input [1:0] select
);

    wire [31:0] ff_out;
    wire [31:0] red_out;
    wire [31:0] xor_out;
    
    dual_edge_ff dff_inst (
        .clk(clk),
        .reset(reset),
        .d(in),
        .q(ff_out)
    );
    
    rising_edge_detector red_inst (
        .clk(clk),
        .reset(reset),
        .in(in),
        .out(red_out)
    );
    
    xor_functional xor_inst (
        .in1(ff_out),
        .in2(red_out),
        .out(xor_out)
    );
    
    assign out = (select == 2'b00) ? ff_out :
                 (select == 2'b01) ? red_out :
                 (select == 2'b10) ? xor_out :
                 32'b0;
    
endmodule
module dual_edge_ff (
    input clk,
    input reset,
    input [31:0] d,
    output [31:0] q
);

    reg [31:0] q1, q2;

    always @(posedge clk or negedge reset) begin
        if (reset == 0) begin
            q1 <= 32'b0;
            q2 <= 32'b0;
        end else begin
            q1 <= d;
            q2 <= q1;
        end
    end

    assign q = q2;

endmodule
module rising_edge_detector (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

    reg [31:0] out_reg;

    always @(posedge clk or negedge reset) begin
        if (reset == 0) begin
            out_reg <= 32'b0;
        end else begin
            out_reg <= (in ^ out_reg) & in;
        end
    end

    assign out = out_reg;

endmodule
module xor_functional (
    input [31:0] in1,
    input [31:0] in2,
    output [31:0] out
);

    assign out = in1 ^ in2;

endmodule