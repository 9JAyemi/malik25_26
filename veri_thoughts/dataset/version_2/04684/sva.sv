module top_module_sva (
    input logic [3:0] in,
    input logic S,
    input logic P,
    input logic Y
);

    // When P is high, Y bypasses the mux and follows in[2].
    check_priority_bypass: assert property (
        @($global_clock) disable iff (1'b0)
        P |-> (Y == in[2])
    );

    // When P is low and S is high, Y selects decoder bit 1.
    check_decode_path_s_high: assert property (
        @($global_clock) disable iff (1'b0)
        (!P && S) |-> (Y == (in == 4'b0001))
    );

    // When P is low and S is low, Y also selects decoder bit 1.
    check_decode_path_s_low: assert property (
        @($global_clock) disable iff (1'b0)
        (!P && !S) |-> (Y == (in == 4'b0001))
    );

    // When P is low, in==1 must drive Y high.
    check_decode_hit: assert property (
        @($global_clock) disable iff (1'b0)
        (!P && (in == 4'b0001)) |-> Y
    );

    // When P is low, any other input must drive Y low.
    check_decode_miss: assert property (
        @($global_clock) disable iff (1'b0)
        (!P && (in != 4'b0001)) |-> !Y
    );

    // Changing only S while P stays low cannot change Y.
    check_s_independent_when_p_low: assert property (
        @($global_clock) disable iff (1'b0)
        ($past(1'b1) && $past(!P) && !P && $stable(in) && $changed(S)) |-> $stable(Y)
    );

    // Changing only S while P stays high cannot change Y.
    check_s_independent_when_p_high: assert property (
        @($global_clock) disable iff (1'b0)
        ($past(1'b1) && $past(P) && P && $stable(in) && $changed(S)) |-> $stable(Y)
    );

    // If all inputs are stable, Y must remain stable.
    check_no_state_when_inputs_stable: assert property (
        @($global_clock) disable iff (1'b0)
        ($past(1'b1) && $stable({in, S, P})) |-> $stable(Y)
    );

    // The observable output matches the full combinational function.
    check_full_function: assert property (
        @($global_clock) disable iff (1'b0)
        Y == (P ? in[2] : (in == 4'b0001))
    );

endmodule