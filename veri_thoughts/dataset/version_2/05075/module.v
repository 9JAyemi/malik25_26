
module bit_change_detector (
    input clk,
    input [15:0] in,
    input reset, // Added reset input
    output reg out
);

    reg [15:0] prev_in;

    always @(posedge clk) begin
        if (reset) begin
            out <= 0;
            prev_in <= 0;
        end else begin
            if (in != prev_in) begin
                out <= 1;
                prev_in <= in;
            end else begin
                out <= 0;
            end
        end
    end
endmodule

module register_module (
    input clk,
    input reset, // Added reset input
    input [15:0] in,
    output reg [15:0] out
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 0;
        end else begin
            out <= in;
        end
    end
endmodule

module control_logic (
    input select,
    input bit_change_detector_out,
    input [15:0] register_out,
    output out
);

    assign out = select ? register_out : bit_change_detector_out;

endmodule

module top_module (
    input clk,
    input reset, // Added reset input
    input [15:0] in,
    input select,
    output out
);

    wire bit_change_detector_out;
    wire [15:0] register_out;

    bit_change_detector bit_change_detector_inst (
        .clk(clk),
        .in(in),
        .reset(reset), // Connected reset signal
        .out(bit_change_detector_out)
    );

    register_module register_inst (
        .clk(clk),
        .reset(reset), // Connected reset signal
        .in(in),
        .out(register_out)
    );

    control_logic control_logic_inst (
        .select(select),
        .bit_change_detector_out(bit_change_detector_out),
        .register_out(register_out),
        .out(out)
    );

endmodule
