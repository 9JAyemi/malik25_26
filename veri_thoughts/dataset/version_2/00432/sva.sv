module filter_sva (
    input logic        clock,
    input logic [31:0] indata,
    input logic [31:0] indata180,
    input logic [31:0] outdata,
    input logic [31:0] dly_indata,
    input logic [31:0] next_dly_indata,
    input logic [31:0] dly_indata180,
    input logic [31:0] next_dly_indata180,
    input logic [31:0] next_outdata
);

    property p_dly_indata_loads_next_dly_indata;
        logic [31:0] captured_next_dly_indata;
        @(posedge clock)
            (1'b1, captured_next_dly_indata = next_dly_indata) |=> (dly_indata == captured_next_dly_indata);
    endproperty

    property p_dly_indata180_loads_next_dly_indata180;
        logic [31:0] captured_next_dly_indata180;
        @(posedge clock)
            (1'b1, captured_next_dly_indata180 = next_dly_indata180) |=> (dly_indata180 == captured_next_dly_indata180);
    endproperty

    property p_outdata_loads_next_outdata;
        logic [31:0] captured_next_outdata;
        @(posedge clock)
            (1'b1, captured_next_outdata = next_outdata) |=> (outdata == captured_next_outdata);
    endproperty

    property p_port_level_two_cycle_recurrence;
        logic [31:0] in0, gate0, out1, in1;
        @(posedge clock)
            (1'b1, in0 = indata, gate0 = indata180) ##1
            (1'b1, out1 = outdata, in1 = indata) |=> (outdata == ((out1 | in0 | in1) & gate0));
    endproperty

    // next_dly_indata mirrors indata in the combinational next-state logic.
    check_next_dly_indata_matches_indata: assert property (
        @(posedge clock) next_dly_indata == indata
    );

    // next_dly_indata180 mirrors indata180 in the combinational next-state logic.
    check_next_dly_indata180_matches_indata180: assert property (
        @(posedge clock) next_dly_indata180 == indata180
    );

    // next_outdata matches the implemented OR-then-mask expression.
    check_next_outdata_matches_expression: assert property (
        @(posedge clock) next_outdata == ((outdata | dly_indata | indata) & dly_indata180)
    );

    // dly_indata loads the previously computed next_dly_indata value.
    check_dly_indata_loads_next_dly_indata: assert property (p_dly_indata_loads_next_dly_indata);

    // dly_indata180 loads the previously computed next_dly_indata180 value.
    check_dly_indata180_loads_next_dly_indata180: assert property (p_dly_indata180_loads_next_dly_indata180);

    // outdata loads the previously computed next_outdata value.
    check_outdata_loads_next_outdata: assert property (p_outdata_loads_next_outdata);

    // next_outdata cannot set bits outside the dly_indata180 mask.
    check_next_outdata_masked_by_dly_indata180: assert property (
        @(posedge clock) (next_outdata & ~dly_indata180) == 32'h0000_0000
    );

    // A zero dly_indata180 mask forces next_outdata to zero.
    check_zero_gate_forces_zero_next_outdata: assert property (
        @(posedge clock) (dly_indata180 == 32'h0000_0000) |-> (next_outdata == 32'h0000_0000)
    );

    // An all-ones dly_indata180 mask makes next_outdata equal the OR term.
    check_full_gate_passes_or_term: assert property (
        @(posedge clock) (dly_indata180 == 32'hFFFF_FFFF) |-> (next_outdata == (outdata | dly_indata | indata))
    );

    // The top-level output follows the same two-cycle recurrence seen at the ports.
    check_port_level_two_cycle_recurrence: assert property (p_port_level_two_cycle_recurrence);

endmodule