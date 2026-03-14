module mux4_sva (
    input  logic A0,
    input  logic A1,
    input  logic A2,
    input  logic A3,
    input  logic S0,
    input  logic S1,
    input  logic X,
    input  logic VPB,
    input  logic VPWR,
    input  logic VGND,
    input  logic VNB,
    // Internal RTL signals (connect via bind or hierarchical reference)
    input  logic [3:0] inputs,
    input  logic [1:0] select
);
    ///// Output function /////
    // X equals OR-reduction of inputs on S0 clock.
    check_x_is_or_inputs_s0: assert property (
        @(posedge S0) X == (inputs[3] | inputs[2] | inputs[1] | inputs[0])
    );
    // X equals OR-reduction of inputs on S1 clock.
    check_x_is_or_inputs_s1: assert property (
        @(posedge S1) X == (inputs[3] | inputs[2] | inputs[1] | inputs[0])
    );

    ///// Combinational decode of inputs from select /////
    // For select == 2'b00, inputs routes A0 to bit[3].
    check_inputs_map_sel_00: assert property (
        @(posedge S0) (select == 2'b00) |-> (inputs == {A0, 1'b0, 1'b0, 1'b0})
    );
    // For select == 2'b01, inputs routes A1 to bit[2].
    check_inputs_map_sel_01: assert property (
        @(posedge S0) (select == 2'b01) |-> (inputs == {1'b0, A1, 1'b0, 1'b0})
    );
    // For select == 2'b10, inputs routes A2 to bit[1].
    check_inputs_map_sel_10: assert property (
        @(posedge S0) (select == 2'b10) |-> (inputs == {1'b0, 1'b0, A2, 1'b0})
    );
    // For select == 2'b11, inputs routes A3 to bit[0].
    check_inputs_map_sel_11: assert property (
        @(posedge S0) (select == 2'b11) |-> (inputs == {1'b0, 1'b0, 1'b0, A3})
    );
    // inputs is one-hot or zero (by construction of the decoder).
    check_inputs_onehot0: assert property (
        @(posedge S0) $onehot0(inputs)
    );

    ///// X equals the selected A input /////
    // When select == 2'b00, X equals A0.
    check_x_map_sel_00: assert property (
        @(posedge S0) (select == 2'b00) |-> (X == A0)
    );
    // When select == 2'b01, X equals A1.
    check_x_map_sel_01: assert property (
        @(posedge S0) (select == 2'b01) |-> (X == A1)
    );
    // When select == 2'b10, X equals A2.
    check_x_map_sel_10: assert property (
        @(posedge S0) (select == 2'b10) |-> (X == A2)
    );
    // When select == 2'b11, X equals A3.
    check_x_map_sel_11: assert property (
        @(posedge S0) (select == 2'b11) |-> (X == A3)
    );

    ///// Select flops behavior /////
    // Posedge S0 causes select[0] to be 1 by the next S0 edge.
    check_select0_sets_next: assert property (
        @(posedge S0) 1'b1 |=> (select[0] == 1'b1)
    );
    // Posedge S1 causes select[1] to be 1 by the next S1 edge.
    check_select1_sets_next: assert property (
        @(posedge S1) 1'b1 |=> (select[1] == 1'b1)
    );
endmodule