module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d1,   // Input for multiplexer
    input [7:0] d2,   // Input for multiplexer
    input sel,        // Select input for multiplexer
    output [7:0] q    // Output from functional module
);

    // Counter module
    reg [3:0] count;
    always @(posedge clk) begin
        if (reset) begin
            count <= 4'b0000;
        end else begin
            count <= count + 1;
        end
    end
    
    // Multiplexer module
    wire [7:0] mux_out;
    mux_2to1 mux_inst (
        .a(d1),
        .b(d2),
        .sel(sel),
        .out(mux_out)
    );
    
    // Functional module
    wire [7:0] sum;
    assign sum = count + mux_out;
    
    // Output
    assign q = sum;

endmodule

// 2-to-1 multiplexer module
module mux_2to1 (
    input [7:0] a,
    input [7:0] b,
    input sel,
    output reg [7:0] out
);
    always @(*) begin
        if (sel) begin
            out = b;
        end else begin
            out = a;
        end
    end
endmodule