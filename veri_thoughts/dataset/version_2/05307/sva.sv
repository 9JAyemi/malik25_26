module DNA_PORT_sva #(
    parameter [56:0] SIM_DNA_VALUE = 57'h0
) (
    input logic        DOUT,
    input logic        CLK,
    input logic        DIN,
    input logic        READ,
    input logic        SHIFT,
    input logic [56:0] dna_val,
    input logic        dout_out
);

    localparam int MAX_DNA_BITS = 57;
    localparam int MSB_DNA_BITS = MAX_DNA_BITS - 1;

    // DOUT is always driven from dout_out.
    check_dout_matches_internal_reg: assert property (
        @(posedge CLK) DOUT === dout_out
    );

    // READ reloads the DNA register with the configured value.
    check_read_reloads_dna_value: assert property (
        @(posedge CLK) READ |=> (dna_val == SIM_DNA_VALUE)
    );

    // READ forces the output register high.
    check_read_sets_dout_high: assert property (
        @(posedge CLK) READ |=> (dout_out == 1'b1)
    );

    // READ has priority over SHIFT when both are asserted.
    check_read_has_priority_over_shift: assert property (
        @(posedge CLK) (READ && SHIFT) |=> ((dna_val == SIM_DNA_VALUE) && (dout_out == 1'b1))
    );

    // SHIFT copies the previous MSB of dna_val to dout_out.
    check_shift_updates_dout_from_msb: assert property (
        @(posedge CLK) (!READ && SHIFT) |=> (dout_out == $past(dna_val[MSB_DNA_BITS]))
    );

    // SHIFT left-shifts dna_val and shifts DIN into bit 0.
    check_shift_updates_dna_register: assert property (
        @(posedge CLK) (!READ && SHIFT) |=> (dna_val == {$past(dna_val[MSB_DNA_BITS-1:0]), $past(DIN)})
    );

    // With neither READ nor SHIFT asserted, dna_val holds its value.
    check_idle_holds_dna_register: assert property (
        @(posedge CLK) (!READ && !SHIFT) |=> (dna_val == $past(dna_val))
    );

    // With neither READ nor SHIFT asserted, dout_out holds its value.
    check_idle_holds_dout_register: assert property (
        @(posedge CLK) (!READ && !SHIFT) |=> (dout_out === $past(dout_out))
    );

endmodule