module FrequencyCounter_sva (
    input logic clk,
    input logic freqin,
    input logic [23:0] frequency,

    // Internal DUT signals (bind these from the instance)
    input logic [23:0] counter,
    input logic [23:0] freq,
    input logic [23:0] secondcounter,
    input logic stopin,
    input logic inreseted
);
    // Mirror of DUT parameter
    localparam logic [23:0] SECONDCOUNT = 24'd8001800;

    ///// Output mapping /////
    // Output port mirrors internal freq register.
    check_frequency_tied_to_internal: assert property (
        @(posedge clk) frequency == freq
    );

    ///// Window hit behavior /////
    // When secondcounter hits SECONDCOUNT, it resets to 0 on that update.
    check_secondcounter_resets_on_hit: assert property (
        @(posedge clk) (secondcounter == SECONDCOUNT) |=> (secondcounter == 24'd0)
    );
    // On hit, freq captures 2*counter from that cycle.
    check_freq_updates_on_hit: assert property (
        @(posedge clk) (secondcounter == SECONDCOUNT) |=> (freq == ($past(counter) << 1))
    );
    // On hit with inreseted LOW, stopin becomes 1.
    check_stopin_set_on_hit_no_inreseted: assert property (
        @(posedge clk) (secondcounter == SECONDCOUNT && !inreseted) |=> (stopin == 1'b1)
    );

    ///// Stop control /////
    // inreseted HIGH forces stopin LOW on next cycle.
    check_stopin_clears_when_inreseted: assert property (
        @(posedge clk) inreseted |=> (stopin == 1'b0)
    );
    // stopin can only deassert when prior inreseted was HIGH.
    check_stopin_only_deasserts_when_inreseted: assert property (
        @(posedge clk) $fell(stopin) |-> $past(inreseted)
    );
    // stopin can only assert when prior hit occurred and inreseted was LOW.
    check_stopin_only_asserts_on_hit_without_inreseted: assert property (
        @(posedge clk) $rose(stopin) |-> ($past(secondcounter) == SECONDCOUNT && !$past(inreseted))
    );

    ///// secondcounter progression /////
    // While not hit and stopin LOW, secondcounter increments by 1.
    check_secondcounter_increments_when_active: assert property (
        @(posedge clk) (secondcounter != SECONDCOUNT && !stopin) |=> (secondcounter == $past(secondcounter) + 24'd1)
    );
    // While not hit and stopin HIGH, secondcounter holds.
    check_secondcounter_holds_when_stopped: assert property (
        @(posedge clk) (secondcounter != SECONDCOUNT && stopin) |=> (secondcounter == $past(secondcounter))
    );

    ///// freq update qualification /////
    // freq changes only on cycles following a hit.
    check_freq_changes_only_on_hit: assert property (
        @(posedge clk) $changed(freq) |-> ($past(secondcounter) == SECONDCOUNT)
    );

    ///// freqin edge effects (sampled on clk) /////
    // Without a freqin falling edge in the interval, counter holds.
    check_counter_stable_without_fall: assert property (
        @(posedge clk) !$fell(freqin) |-> (counter == $past(counter))
    );
    // A freqin fall while counting increments counter by at least 1 by this sample.
    check_counter_increments_on_fall_while_counting: assert property (
        @(posedge clk) ($fell(freqin) && ($past(stopin) == 1'b0)) |-> (counter >= $past(counter) + 24'd1)
    );
    // A freqin fall while stopped resets counter to 0 and sets inreseted.
    check_counter_reset_and_inreseted_set_on_fall_while_stopped: assert property (
        @(posedge clk) ($fell(freqin) && ($past(stopin) == 1'b1)) |-> (counter == 24'd0 && inreseted == 1'b1)
    );
    // A freqin fall while counting clears inreseted to 0.
    check_inreseted_cleared_on_fall_while_counting: assert property (
        @(posedge clk) ($fell(freqin) && ($past(stopin) == 1'b0)) |-> (inreseted == 1'b0)
    );

endmodule