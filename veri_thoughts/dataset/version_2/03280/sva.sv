module sky130_fd_sc_ms__clkdlyinv5sd1_sva (
    input logic Y,
    input logic A
);

    // No clock or reset exists in the RTL.
    // Logic is purely combinational: Y is the buffered inversion of A.

    // Before A rises, the inverter output must be high.
    check_a_rise_starts_with_y_high: assert property (
        @(posedge A) Y === 1'b1
    );

    // Before A falls, the inverter output must be low.
    check_a_fall_starts_with_y_low: assert property (
        @(negedge A) Y === 1'b0
    );

    // Before Y rises, the input must be high.
    check_y_rise_starts_with_a_high: assert property (
        @(posedge Y) A === 1'b1
    );

    // Before Y falls, the input must be low.
    check_y_fall_starts_with_a_low: assert property (
        @(negedge Y) A === 1'b0
    );

endmodule