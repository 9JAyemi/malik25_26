module interrupt_controller_sva (
    input logic clk,
    input logic clk7_en,
    input logic wr,
    input logic reset,
    input logic icrs,
    input logic ta,
    input logic tb,
    input logic alrm,
    input logic flag,
    input logic ser,
    input logic [7:0] data_in,
    input logic [7:0] data_out,
    input logic irq,
    // Internal DUT signals (for binding)
    input logic [4:0] icr,
    input logic [4:0] icrmask
);
    ///// Combinational outputs /////
    // irq equals masked-OR of icr bits.
    check_irq_definition: assert property (
        @(posedge clk) disable iff (reset)
        irq == ((icrmask[0] & icr[0])
              | (icrmask[1] & icr[1])
              | (icrmask[2] & icr[2])
              | (icrmask[3] & icr[3])
              | (icrmask[4] & icr[4]))
    );

    // When reading ICR (icrs && !wr), data_out is {irq,2'b00,icr}.
    check_data_out_on_read: assert property (
        @(posedge clk) disable iff (reset)
        (icrs && !wr) |-> (data_out == {irq, 2'b00, icr})
    );

    // When not reading ICR, data_out is 8'h00.
    check_data_out_when_not_read: assert property (
        @(posedge clk) disable iff (reset)
        !(icrs && !wr) |-> (data_out == 8'h00)
    );

    ///// Synchronous reset behavior (gated by clk7_en) /////
    // When clk7_en and reset are high, icrmask clears next cycle.
    reset_clears_icrmask: assert property (
        @(posedge clk)
        (clk7_en && reset) |=> (icrmask == 5'b0_00000)
    );

    // When clk7_en and reset are high, icr clears next cycle.
    reset_clears_icr: assert property (
        @(posedge clk)
        (clk7_en && reset) |=> (icr == 5'b0_00000)
    );

    ///// icrmask write semantics /////
    // On write with data_in[7]==1, set selected icrmask bits next cycle.
    write_sets_mask_bits: assert property (
        @(posedge clk) disable iff (reset)
        (clk7_en && icrs && wr && (data_in[7] == 1'b1)) |=> (icrmask == ($past(icrmask) | $past(data_in[4:0])))
    );

    // On write with data_in[7]==0, clear selected icrmask bits next cycle.
    write_clears_mask_bits: assert property (
        @(posedge clk) disable iff (reset)
        (clk7_en && icrs && wr && (data_in[7] == 1'b0)) |=> (icrmask == ($past(icrmask) & (~$past(data_in[4:0]))))
    );

    // Without a qualifying write, icrmask holds value on next cycle.
    icrmask_holds_without_write: assert property (
        @(posedge clk) disable iff (reset)
        (clk7_en && !(icrs && wr)) |=> (icrmask == $past(icrmask))
    );

    ///// clk7_en gating /////
    // When clk7_en is low, icr and icrmask hold.
    regs_hold_when_clk7_en_low: assert property (
        @(posedge clk) disable iff (reset)
        (!clk7_en) |=> (icr == $past(icr)) && (icrmask == $past(icrmask))
    );

    ///// icr update semantics /////
    // On read (icrs && !wr), icr captures current input sources next cycle.
    icr_captures_inputs_on_read: assert property (
        @(posedge clk) disable iff (reset)
        (clk7_en && icrs && !wr) |=> (icr[0] == $past(ta))
                                && (icr[1] == $past(tb))
                                && (icr[2] == $past(alrm))
                                && (icr[3] == $past(ser))
                                && (icr[4] == $past(flag))
    );

    // When not reading, icr bits OR-latch with their respective sources next cycle.
    icr_or_latches_when_not_read: assert property (
        @(posedge clk) disable iff (reset)
        (clk7_en && !(icrs && !wr)) |=> (icr[0] == ($past(icr[0]) | $past(ta)))
                                   && (icr[1] == ($past(icr[1]) | $past(tb)))
                                   && (icr[2] == ($past(icr[2]) | $past(alrm)))
                                   && (icr[3] == ($past(icr[3]) | $past(ser)))
                                   && (icr[4] == ($past(icr[4]) | $past(flag)))
    );

endmodule