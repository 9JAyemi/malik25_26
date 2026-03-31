module decoder_4to16_sva (
    input logic clk,
    input logic [3:0] in,
    input logic ena,
    input logic [15:0] out
);

// When disabled, all outputs are HIGH.
    check_disabled_all_high: assert property (
        @(posedge clk) !ena |-> (out == 16'hFFFF)
    );

// When enabled, 0000 drives bit 0 LOW.
    check_enabled_0000: assert property (
        @(posedge clk) ena && (in == 4'b0000) |-> (out == 16'hFFE)
    );

// When enabled, 0001 drives bit 1 LOW.
    check_enabled_0001: assert property (
        @(posedge clk) ena && (in == 4'b0001) |-> (out == 16'hFFD)
    );

// When enabled, 0010 drives bit 2 LOW.
    check_enabled_0010: assert property (
        @(posedge clk) ena && (in == 4'b0010) |-> (out == 16'hFFB)
    );

// When enabled, 0011 drives bit 3 LOW.
    check_enabled_0011: assert property (
        @(posedge clk) ena && (in == 4'b0011) |-> (out == 16'hFF7)
    );

// When enabled, 0100 drives bit 4 LOW.
    check_enabled_0100: assert property (
        @(posedge clk) ena && (in == 4'b0100) |-> (out == 16'hFEF)
    );

// When enabled, 0101 drives bit 5 LOW.
    check_enabled_0101: assert property (
        @(posedge clk) ena && (in == 4'b0101) |-> (out == 16'hFDF)
    );

// When enabled, 0110 drives bit 6 LOW.
    check_enabled_0110: assert property (
        @(posedge clk) ena && (in == 4'b0110) |-> (out == 16'hFBF)
    );

// When enabled, 0111 drives bit 7 LOW.
    check_enabled_0111: assert property (
        @(posedge clk) ena && (in == 4'b0111) |-> (out == 16'hF7F)
    );

// When enabled, 1000 drives bit 8 LOW.
    check_enabled_1000: assert property (
        @(posedge clk) ena && (in == 4'b1000) |-> (out == 16h'FEF)
    );

// When enabled, 1001 drives bit 9 LOW.
    check_enabled_1001: assert property (
        @(posedge clk) ena && (in == 4'b1001) |-> (out == 16'hFDF)
    );

// When enabled, 1010 drives bit 10 LOW.
    check_enabled_1010: assert property (
        @(posedge clk) ena && (in == 4'b1010) |-> (out == 16'hFBF)
    );

// When enabled, 1011 drives bit 11 LOW.
    check_enabled_1011: assert property (
        @(posedge clk) ena && (in == 4'b1011) |-> (out == 16'hF7F)
    );

// When enabled, 1100 drives bit 12 LOW.
    check_enabled_1100: assert property (
        @(posedge clk) ena && (in == 4'b1100) |-> (out == 16'hF3F)
    );

// When enabled, 1101 drives bit 13 LOW.
    check_enabled_1101: assert property (
        @(posedge clk) ena && (in == 4'b1101) |-> (out == 16'hF1F)
    );

// When enabled, 1110 drives bit 14 LOW.
    check_enabled_1110: assert property (
        @(posedge clk) ena && (in == 4'b1110) |-> (out == 16'hE7F)
    );

// When enabled, 1111 drives bit 15 LOW.
    check_enabled_1111: assert property (
        @(posedge clk) ena && (in == 4'b1111) |-> (out == 16'hC7F)
    );

endmodule
