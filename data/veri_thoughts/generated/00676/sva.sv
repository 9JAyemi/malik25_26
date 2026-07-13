module my_module_sva (
    input logic in,
    input logic clk,
    input logic fr_a,
    input logic fr_b,
    input logic fr_chk
);
    ///// Sequential sampling /////
    // fr_a samples 'in' on each rising clock (1-cycle latency).
    check_fr_a_samples_in: assert property (
        @(posedge clk) fr_a == $past(in)
    );
    // fr_b samples 'in' on each rising clock (1-cycle latency).
    check_fr_b_samples_in: assert property (
        @(posedge clk) fr_b == $past(in)
    );
    // fr_chk captures LSB of (in + 1), i.e., complement of previous 'in'.
    check_fr_chk_complements_in: assert property (
        @(posedge clk) fr_chk == ~ $past(in)
    );

    ///// Edge propagation /////
    // A rise on 'in' causes a rise on fr_a one cycle later.
    in_rise_to_fr_a_rise: assert property (
        @(posedge clk) $rose(in) |=> $rose(fr_a)
    );
    // A fall on 'in' causes a fall on fr_a one cycle later.
    in_fall_to_fr_a_fall: assert property (
        @(posedge clk) $fell(in) |=> $fell(fr_a)
    );
    // A rise on 'in' causes a rise on fr_b one cycle later.
    in_rise_to_fr_b_rise: assert property (
        @(posedge clk) $rose(in) |=> $rose(fr_b)
    );
    // A fall on 'in' causes a fall on fr_b one cycle later.
    in_fall_to_fr_b_fall: assert property (
        @(posedge clk) $fell(in) |=> $fell(fr_b)
    );
    // A rise on 'in' causes a fall on fr_chk one cycle later.
    in_rise_to_fr_chk_fall: assert property (
        @(posedge clk) $rose(in) |=> $fell(fr_chk)
    );
    // A fall on 'in' causes a rise on fr_chk one cycle later.
    in_fall_to_fr_chk_rise: assert property (
        @(posedge clk) $fell(in) |=> $rose(fr_chk)
    );
endmodule