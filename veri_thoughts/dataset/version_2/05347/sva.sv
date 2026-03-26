module flag_gen_sva (
    input logic clk,
    input logic rst,
    input logic full,
    input logic emptyp,
    input logic wr_en,
    input logic rd_en
);

    // full and emptyp can never be high together.
    check_flags_mutex: assert property (
        @(posedge clk) disable iff (!rst) !(full && emptyp)
    );

    // Idle cycles keep both flags unchanged.
    check_idle_holds_flags: assert property (
        @(posedge clk) disable iff (!rst)
        (!wr_en && !rd_en) |=> ($stable(full) && $stable(emptyp))
    );

    // Simultaneous read and write keep both flags unchanged.
    check_simul_rw_holds_flags: assert property (
        @(posedge clk) disable iff (!rst)
        (wr_en && rd_en) |=> ($stable(full) && $stable(emptyp))
    );

    // When empty, no-write cycles keep emptyp asserted.
    check_empty_without_write_stays_empty: assert property (
        @(posedge clk) disable iff (!rst)
        (emptyp && !wr_en) |=> (emptyp && !full)
    );

    // A write-only cycle from empty clears emptyp.
    check_empty_write_only_clears_empty: assert property (
        @(posedge clk) disable iff (!rst)
        (emptyp && wr_en && !rd_en) |=> (!emptyp && !full)
    );

    // When full, no-read cycles keep full asserted.
    check_full_without_read_stays_full: assert property (
        @(posedge clk) disable iff (!rst)
        (full && !rd_en) |=> (full && !emptyp)
    );

    // A read-only cycle from full clears full.
    check_full_read_only_clears_full: assert property (
        @(posedge clk) disable iff (!rst)
        (full && rd_en && !wr_en) |=> (!full && !emptyp)
    );

    // emptyp can only fall after an empty write-only cycle.
    check_empty_fall_requires_write_only: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(rst) && $fell(emptyp)) |-> $past(emptyp && wr_en && !rd_en)
    );

    // full can only fall after a full read-only cycle.
    check_full_fall_requires_read_only: assert property (
        @(posedge clk) disable iff (!rst)
        ($past(rst) && $fell(full)) |-> $past(full && rd_en && !wr_en)
    );

endmodule