module top_module_sva (
    input logic clk,
    input logic reset,        // Active-high reset
    input logic [3:0] in,
    input logic [1:0] pos,
    input logic [7:0] out
);
    ///// Priority encoder mapping /////
    // If in=1000 then pos must be 11.
    pe_map_in_1000_to_pos_11: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b1000) |-> (pos == 2'b11)
    );
    // If in=0100 then pos must be 10.
    pe_map_in_0100_to_pos_10: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b0100) |-> (pos == 2'b10)
    );
    // If in=0010 then pos must be 01.
    pe_map_in_0010_to_pos_01: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b0010) |-> (pos == 2'b01)
    );
    // If in=0001 then pos must be 00.
    pe_map_in_0001_to_pos_00: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b0001) |-> (pos == 2'b00)
    );
    // For all other in values, pos must be 00 (default case).
    pe_default_others_to_pos_00: assert property (
        @(posedge clk) disable iff (reset) (in != 4'b1000 && in != 4'b0100 && in != 4'b0010 && in != 4'b0001) |-> (pos == 2'b00)
    );
    // pos=11 can only occur when in=1000.
    pe_pos_11_implies_1000: assert property (
        @(posedge clk) disable iff (reset) (pos == 2'b11) |-> (in == 4'b1000)
    );
    // pos=10 can only occur when in=0100.
    pe_pos_10_implies_0100: assert property (
        @(posedge clk) disable iff (reset) (pos == 2'b10) |-> (in == 4'b0100)
    );
    // pos=01 can only occur when in=0010.
    pe_pos_01_implies_0010: assert property (
        @(posedge clk) disable iff (reset) (pos == 2'b01) |-> (in == 4'b0010)
    );
    // pos must be stable across cycles when in is stable (pure combinational mapping).
    pe_pos_stable_when_in_stable: assert property (
        @(posedge clk) disable iff (reset) $stable(in) |-> $stable(pos)
    );

    ///// Counter/out behavior (observed via product) /////
    // While reset is asserted, out must be 0 (count is held at 0).
    out_zero_during_reset: assert property (
        @(posedge clk) reset |-> (out == 8'b0)
    );
    // If in=0000, out must be 0 (multiplication by zero).
    out_zero_when_in_zero: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b0000) |-> (out == 8'b0)
    );
    // If in=0010 (x2), LSB must be 0.
    out_lsb0_zero_when_in_0010: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b0010) |-> (out[0] == 1'b0)
    );
    // If in=0100 (x4), two LSBs must be 0.
    out_lsb01_zero_when_in_0100: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b0100) |-> (out[1:0] == 2'b00)
    );
    // If in=1000 (x8), three LSBs must be 0.
    out_lsb012_zero_when_in_1000: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b1000) |-> (out[2:0] == 3'b000)
    );
    // With in=1000 held stable across cycles, out must increment by 8 (mod 256) each cycle.
    out_increments_by_8_when_in_1000_stable: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) == 1'b0 && $past(in) == 4'b1000 && in == 4'b1000) |-> (out == $past(out) + 8'd8)
    );
    // If in is stable and pos!=11 across cycles (no enable), out must be stable.
    out_stable_when_no_increment: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) == 1'b0 && $past(in) == in && $past(pos) != 2'b11 && pos != 2'b11) |-> $stable(out)
    );
endmodule