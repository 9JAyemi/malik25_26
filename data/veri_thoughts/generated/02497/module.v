module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [255:0] in, // 256-bit input for the multiplexer
    input [7:0] sel,  // 8-bit selection input for the multiplexer
    input direction,   // Direction input for the counter
    output [2:0] count, // 3-bit output from the counter
    output reg out     // 1-bit output from the functional module
);

    // 256-to-1 multiplexer module
    wire [7:0] mux_sel;
    wire mux_out;
    mux_256to1 mux (
        .in(in),
        .sel(mux_sel),
        .out(mux_out)
    );

    // Bidirectional 3-bit counter module
    wire [2:0] counter_out;
    bidir_counter counter (
        .clk(clk),
        .reset(reset),
        .direction(direction),
        .out(counter_out)
    );

    // Functional module that outputs the bitwise AND of the multiplexer and counter outputs
    always @(*) begin
        out = mux_out & counter_out[0];
    end

    // Connect the selection input of the multiplexer to the counter output
    assign mux_sel = counter_out[1:0] + sel;

    // Output the counter output
    assign count = counter_out;

endmodule

// 256-to-1 multiplexer module
module mux_256to1 (
    input [255:0] in, // 256-bit input
    input [7:0] sel,  // 8-bit selection input
    output reg out     // 1-bit output
);

    always @(*) begin
        out = in[sel];
    end

endmodule

// Bidirectional 3-bit counter module
module bidir_counter (
    input clk,
    input reset,      // Synchronous active-high reset
    input direction,   // Direction input
    output reg [2:0] out // 3-bit output
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 3'b0;
        end else if (direction) begin
            out <= out + 1;
        end else begin
            out <= out - 1;
        end
    end

endmodule