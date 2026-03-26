module shift_register_sva (
    input logic       CLK,
    input logic       SI,
    input logic       SO,
    input logic [3:0] Q
);

    // SO always reflects the LSB of Q.
    check_so_matches_q_lsb: assert property (
        @(posedge CLK) SO == Q[0]
    );

    // SI high loads 4'b0001 into Q on the next clock.
    check_si_high_loads_one: assert property (
        @(posedge CLK) SI |=> Q == 4'b0001
    );

    // SI high makes SO high on the next clock.
    check_si_high_sets_so: assert property (
        @(posedge CLK) SI |=> SO == 1'b1
    );

    // SI high clears the upper three bits on the next clock.
    check_si_high_clears_upper_bits: assert property (
        @(posedge CLK) SI |=> Q[3:1] == 3'b000
    );

    // SI low updates Q from the previous Q[2:0] and SO.
    check_si_low_updates_q: assert property (
        @(posedge CLK) !SI |=> Q == {$past(Q[2:0]), $past(SO)}
    );

    // SI low shifts the previous Q[2:0] into Q[3:1].
    check_si_low_updates_upper_bits: assert property (
        @(posedge CLK) !SI |=> Q[3:1] == $past(Q[2:0])
    );

    // SI low keeps SO equal to its previous value.
    check_si_low_holds_so: assert property (
        @(posedge CLK) !SI |=> SO == $past(SO)
    );

    // SI low duplicates the previous SO into Q[1:0].
    check_si_low_duplicates_so_into_low_bits: assert property (
        @(posedge CLK) !SI |=> Q[1:0] == {$past(SO), $past(SO)}
    );

endmodule