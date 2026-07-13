module rotator_sva (
    input logic        clk,
    input logic        load,
    input logic [1:0]  ena,
    input logic [99:0] data,
    input logic [99:0] q
);

    // load captures data on the next clock, regardless of ena.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> q == $past(data)
    );

    // With only ena[1] set, q follows the {q[98:0], q[99]} update.
    check_ena1_updates_with_wrap: assert property (
        @(posedge clk) !load && (ena == 2'b10) |=> q == { $past(q[98:0]), $past(q[99]) }
    );

    // When both enable bits are set, ena[1] has priority over ena[0].
    check_ena1_priority_when_both_high: assert property (
        @(posedge clk) !load && (ena == 2'b11) |=> q == { $past(q[98:0]), $past(q[99]) }
    );

    // With only ena[0] set, the upper 97 bits are cleared by the implemented assignment.
    check_ena0_clears_upper_bits: assert property (
        @(posedge clk) !load && (ena == 2'b01) |=> q[99:3] == 97'b0
    );

    // With only ena[0] set, the low 3 bits match the implemented concatenation.
    check_ena0_updates_low_bits: assert property (
        @(posedge clk) !load && (ena == 2'b01) |=> q[2:0] == { $past(q[1:0]), $past(q[0]) }
    );

    // Without load or enable, q holds its previous value.
    check_hold_when_idle: assert property (
        @(posedge clk) !load && (ena == 2'b00) |=> q == $past(q)
    );

endmodule