module timer_sva (
    input logic CLK_I,
    input logic RST_I,

    input logic [31:2] ADR_I,
    input logic CYC_I,
    input logic STB_I,
    input logic WE_I,

    input logic RTY_O,
    input logic interrupt_o,

    // Internal signal from DUT
    input logic [27:0] counter
);

    // Reset sets RTY_O, interrupt_o, and counter to 0 on the next cycle.
    reset_clears_outputs_and_counter: assert property (
        @(posedge CLK_I) RST_I |=> (RTY_O == 1'b0) && (interrupt_o == 1'b0) && (counter == 28'd0)
    );

    // Counter never exceeds terminal value 28'h00FFFFF.
    check_counter_bounded: assert property (
        @(posedge CLK_I) disable iff (RST_I) counter <= 28'h00FFFFF
    );

    // When not at terminal count, counter increments by 1 next cycle.
    inc_when_not_at_limit: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            (counter != 28'h00FFFFF) |=> (counter == $past(counter) + 28'd1)
    );

    // When not at terminal count, RTY_O is driven LOW next cycle.
    rty_low_when_not_at_limit: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            (counter != 28'h00FFFFF) |=> (RTY_O == 1'b0)
    );

    // When not at terminal count, interrupt_o is unchanged next cycle.
    interrupt_unchanged_when_not_at_limit: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            (counter != 28'h00FFFFF) |=> (interrupt_o == $past(interrupt_o))
    );

    // When at terminal count and matching read access with interrupt_o==1, clear: RTY_O=1, interrupt_o=0, counter=0 next cycle.
    clear_when_limit_and_bus_read: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            (counter == 28'h00FFFFF) &&
            (ADR_I == {27'b1111_1111_1111_1111_1111_1111_111, 3'b001}) &&
            (CYC_I == 1'b1) && (STB_I == 1'b1) && (WE_I == 1'b0) && (interrupt_o == 1'b1)
            |=> (RTY_O == 1'b1) && (interrupt_o == 1'b0) && (counter == 28'd0)
    );

    // When at terminal count without the matching read access, interrupt_o is set HIGH next cycle.
    set_interrupt_when_limit_without_clear: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            (counter == 28'h00FFFFF) &&
            !((ADR_I == {27'b1111_1111_1111_1111_1111_1111_111, 3'b001}) &&
              (CYC_I == 1'b1) && (STB_I == 1'b1) && (WE_I == 1'b0) && (interrupt_o == 1'b1))
            |=> (interrupt_o == 1'b1)
    );

    // When at terminal count without the matching read access, counter holds its value next cycle.
    hold_counter_when_limit_without_clear: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            (counter == 28'h00FFFFF) &&
            !((ADR_I == {27'b1111_1111_1111_1111_1111_1111_111, 3'b001}) &&
              (CYC_I == 1'b1) && (STB_I == 1'b1) && (WE_I == 1'b0) && (interrupt_o == 1'b1))
            |=> (counter == $past(counter))
    );

    // When at terminal count without the matching read access, RTY_O holds its value next cycle.
    hold_rty_when_limit_without_clear: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            (counter == 28'h00FFFFF) &&
            !((ADR_I == {27'b1111_1111_1111_1111_1111_1111_111, 3'b001}) &&
              (CYC_I == 1'b1) && (STB_I == 1'b1) && (WE_I == 1'b0) && (interrupt_o == 1'b1))
            |=> (RTY_O == $past(RTY_O))
    );

    // A rising edge on RTY_O implies previous cycle was the matching read at terminal count.
    rty_rose_only_from_clear: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            $rose(RTY_O) |-> ($past(counter) == 28'h00FFFFF) &&
                           ($past(ADR_I) == {27'b1111_1111_1111_1111_1111_1111_111, 3'b001}) &&
                           ($past(CYC_I) == 1'b1) && ($past(STB_I) == 1'b1) &&
                           ($past(WE_I) == 1'b0) && ($past(interrupt_o) == 1'b1)
    );

    // A rising edge on interrupt_o implies previous cycle was terminal count without the matching read.
    interrupt_rose_only_from_limit_no_clear: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            $rose(interrupt_o) |-> ($past(counter) == 28'h00FFFFF) &&
                                 !(( $past(ADR_I) == {27'b1111_1111_1111_1111_1111_1111_111, 3'b001}) &&
                                    ($past(CYC_I) == 1'b1) && ($past(STB_I) == 1'b1) &&
                                    ($past(WE_I) == 1'b0) && ($past(interrupt_o) == 1'b1))
    );

    // RTY_O pulses for a single cycle.
    rty_is_single_cycle_pulse: assert property (
        @(posedge CLK_I) disable iff (RST_I)
            RTY_O |=> !RTY_O
    );

endmodule