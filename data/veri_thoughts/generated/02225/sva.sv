module trigterm_range_bit_sva (
    input logic sti_data,
    input logic clk,
    input logic wrenb,
    input logic din,
    input logic dout,
    input logic cin,
    input logic cout,
    input logic hit,
    // Internal signal from RTL
    input logic [15:0] mem
);

    ///// Sequential memory behavior /////
    // When wrenb is HIGH, mem shifts left and loads din into bit 0 on next cycle.
    check_mem_shift_on_write: assert property (
        @(posedge clk) disable iff ($initstate)
            wrenb |=> (mem == { $past(mem[14:0]), $past(din) })
    );

    // When wrenb is LOW, mem holds its previous value.
    check_mem_hold_without_write: assert property (
        @(posedge clk) disable iff ($initstate)
            !wrenb |=> (mem == $past(mem))
    );

    ///// Output tap and update timing /////
    // dout reflects the MSB of mem.
    check_dout_is_msb_of_mem: assert property (
        @(posedge clk) disable iff ($initstate)
            dout == mem[15]
    );

    // On a write, next-cycle dout equals previous mem[14].
    check_dout_updates_on_write: assert property (
        @(posedge clk) disable iff ($initstate)
            wrenb |=> (dout == $past(mem[14]))
    );

    // Without write, dout holds its previous value.
    check_dout_stable_when_no_write: assert property (
        @(posedge clk) disable iff ($initstate)
            !wrenb |=> (dout == $past(dout))
    );

    ///// Combinational selects /////
    // hit equals the selected mem bit indexed by {3'b000, sti_data}.
    check_hit_equals_selected_mem_bit: assert property (
        @(posedge clk) disable iff ($initstate)
            hit == mem[{3'b000, sti_data}]
    );

    // cout implements mux: if hit is 1 choose cin, else choose din.
    check_cout_mux_function: assert property (
        @(posedge clk) disable iff ($initstate)
            cout == (hit ? cin : din)
    );

    // cout must always equal one of its inputs.
    check_cout_is_one_of_inputs: assert property (
        @(posedge clk) disable iff ($initstate)
            (cout == cin) || (cout == din)
    );

    // If cout differs from din, hit must be HIGH.
    check_cout_ne_din_implies_hit: assert property (
        @(posedge clk) disable iff ($initstate)
            (cout != din) |-> hit
    );

    // If cout differs from cin, hit must be LOW.
    check_cout_ne_cin_implies_not_hit: assert property (
        @(posedge clk) disable iff ($initstate)
            (cout != cin) |-> !hit
    );

endmodule