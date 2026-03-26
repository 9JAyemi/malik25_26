
module top_module (
    input clk,
    input wire [15:0] in,
    input [7:0] in_edge,
    output wire anyedge
);

    wire [7:0] upper_byte;
    wire [7:0] lower_byte;
    wire upper_edge;
    wire lower_edge;

    // Split input into upper and lower bytes
    byte_splitter byte_splitter_inst (
        .in(in),
        .upper_byte(upper_byte),
        .lower_byte(lower_byte)
    );

    // Detect edge transitions in upper and lower bytes
    edge_detector edge_detector_upper_inst (
        .clk(clk),
        .in(upper_byte),
        .out(upper_edge)
    );

    edge_detector edge_detector_lower_inst (
        .clk(clk),
        .in(lower_byte),
        .out(lower_edge)
    );

    // Combine edge transitions from upper and lower bytes
    or_gate or_gate_inst (
        .in1(upper_edge),
        .in2(lower_edge),
        .out(anyedge)
    );

    // Output any edge transition
    assign anyedge = anyedge;

endmodule
module byte_splitter (
    input wire [15:0] in,
    output reg [7:0] upper_byte,
    output reg [7:0] lower_byte
);

    always @(*) begin
        upper_byte = in[15:8];
        lower_byte = in[7:0];
    end

endmodule
module edge_detector (
    input clk,
    input [7:0] in,
    output reg out
);

    reg [7:0] prev_in;

    always @(posedge clk) begin
        if (in != prev_in) begin
            out <= 1;
        end else begin
            out <= 0;
        end
        prev_in <= in;
    end

endmodule
module or_gate (
    input wire in1,
    input wire in2,
    output reg out
);

    always @(*) begin
        out = in1 | in2;
    end

endmodule