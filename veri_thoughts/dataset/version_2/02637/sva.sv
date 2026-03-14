module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] A,
    input logic [1:0] B,
    input logic [7:0] Q
);
    // 4-bit rotate-left helper matching inverse of DUT's rotate-right
    function automatic logic [3:0] rotl4 (input logic [3:0] x, input logic [1:0] b);
        case (b)
            2'b00: rotl4 = x;
            2'b01: rotl4 = {x[2:0], x[3]};
            2'b10: rotl4 = {x[1:0], x[3:2]};
            2'b11: rotl4 = {x[0],   x[3:1]};
        endcase
    endfunction

    ///// Reset behavior /////
    // When reset is asserted, the top output is zero.
    reset_clears_Q: assert property (
        @(posedge clk) reset |-> (Q == 8'h00)
    );

    ///// Structural arithmetic invariants /////
    // Upper nibble is always zero (adder adds zero to a 4-bit value).
    high_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) (Q[7:4] == 4'b0000)
    );

    ///// Counter progression observed via rotated domain /////
    // Rotated domain value increases by 1 each cycle (mod 16).
    rotated_domain_increments_general: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> ( rotl4(Q[3:0], B) == ((rotl4($past(Q[3:0]), $past(B)) + 5'd1) & 4'hF) )
    );

    // With B=00 stable, low nibble increments by 1 (mod 16).
    rotated_domain_increments_B00: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && (B == 2'b00) && ($past(B) == 2'b00))
            |-> ( Q[3:0] == (($past(Q[3:0]) + 5'd1) & 4'hF) )
    );

    // With B=01 stable, rotl1(low nibble) increments by 1 (mod 16).
    rotated_domain_increments_B01: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && (B == 2'b01) && ($past(B) == 2'b01))
            |-> ( rotl4(Q[3:0], 2'b01) == ((rotl4($past(Q[3:0]), 2'b01) + 5'd1) & 4'hF) )
    );

    // With B=10 stable, rotl2(low nibble) increments by 1 (mod 16).
    rotated_domain_increments_B10: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && (B == 2'b10) && ($past(B) == 2'b10))
            |-> ( rotl4(Q[3:0], 2'b10) == ((rotl4($past(Q[3:0]), 2'b10) + 5'd1) & 4'hF) )
    );

    // With B=11 stable, rotl3(low nibble) increments by 1 (mod 16).
    rotated_domain_increments_B11: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && (B == 2'b11) && ($past(B) == 2'b11))
            |-> ( rotl4(Q[3:0], 2'b11) == ((rotl4($past(Q[3:0]), 2'b11) + 5'd1) & 4'hF) )
    );

    // When the rotated domain hits 0xF, it wraps to 0x0 next cycle.
    rotated_domain_wraps_after_F: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && (rotl4($past(Q[3:0]), $past(B)) == 4'hF))
            |-> (rotl4(Q[3:0], B) == 4'h0)
    );
endmodule