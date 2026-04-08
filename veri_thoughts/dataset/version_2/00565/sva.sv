module AddressGenerator_sva (
    input logic        clk,
    input logic        ce,
    input logic [4:0]  Operation,
    input logic [1:0]  MuxCtrl,
    input logic [7:0]  DataBus,
    input logic [7:0]  T,
    input logic [7:0]  X,
    input logic [7:0]  Y,
    input logic [15:0] AX,
    input logic        Carry
);

    property p_carry_matches_selected_sum;
        logic [8:0] expected_sum;
        @(posedge clk)
            (1'b1, expected_sum = {1'b0, (MuxCtrl[1] ? T : AX[7:0])} + {1'b0, (MuxCtrl[0] ? Y : X)})
            |-> (Carry == expected_sum[8]);
    endproperty

    property p_ax_holds_when_ce_low;
        logic [15:0] held_ax;
        @(posedge clk)
            (!ce, held_ax = AX)
            |=> (AX == held_ax);
    endproperty

    property p_al_holds_when_not_enabled;
        logic [7:0] held_al;
        @(posedge clk)
            (ce && !Operation[4], held_al = AX[7:0])
            |=> (AX[7:0] == held_al);
    endproperty

    property p_al_loads_newal;
        logic [7:0] expected_al;
        @(posedge clk)
            (ce && (Operation[4:2] == 3'b100),
             expected_al = (MuxCtrl[1] ? T : AX[7:0]) + (MuxCtrl[0] ? Y : X))
            |=> (AX[7:0] == expected_al);
    endproperty

    property p_al_loads_databus;
        logic [7:0] expected_al;
        @(posedge clk)
            (ce && (Operation[4:2] == 3'b101), expected_al = DataBus)
            |=> (AX[7:0] == expected_al);
    endproperty

    property p_al_loads_incremented_al;
        logic [7:0] expected_al;
        @(posedge clk)
            (ce && (Operation[4:2] == 3'b110) && !Operation[1], expected_al = AX[7:0] + 8'h01)
            |=> (AX[7:0] == expected_al);
    endproperty

    property p_al_loads_t;
        logic [7:0] expected_al;
        @(posedge clk)
            (ce && (Operation[4:2] == 3'b111), expected_al = T)
            |=> (AX[7:0] == expected_al);
    endproperty

    property p_ah_holds;
        logic [7:0] held_ah;
        @(posedge clk)
            (ce && (Operation[1:0] == 2'b00), held_ah = AX[15:8])
            |=> (AX[15:8] == held_ah);
    endproperty

    property p_ah_clears;
        @(posedge clk)
            (ce && (Operation[1:0] == 2'b01))
            |=> (AX[15:8] == 8'h00);
    endproperty

    property p_ah_loads_databus;
        logic [7:0] expected_ah;
        @(posedge clk)
            (ce && (Operation[1:0] == 2'b11), expected_ah = DataBus)
            |=> (AX[15:8] == expected_ah);
    endproperty

    // Carry is the carry-out of the selected 8-bit addition.
    check_carry_matches_selected_sum: assert property (p_carry_matches_selected_sum);

    // AX holds its value when clock enable is low.
    check_ax_holds_when_ce_low: assert property (p_ax_holds_when_ce_low);

    // AL holds when the AL update enable bit is not set.
    check_al_holds_when_not_enabled: assert property (p_al_holds_when_not_enabled);

    // AL loads the selected sum when ALCtrl selects NewAL.
    check_al_loads_newal: assert property (p_al_loads_newal);

    // AL loads DataBus when ALCtrl selects the bus.
    check_al_loads_databus: assert property (p_al_loads_databus);

    // AL increments from its current value when TmpAdd uses AL plus one.
    check_al_loads_incremented_al: assert property (p_al_loads_incremented_al);

    // AL loads T when ALCtrl selects T.
    check_al_loads_t: assert property (p_al_loads_t);

    // AH holds when AHCtrl selects hold.
    check_ah_holds: assert property (p_ah_holds);

    // AH clears to zero when AHCtrl selects zero.
    check_ah_clears: assert property (p_ah_clears);

    // AH loads DataBus when AHCtrl selects the bus.
    check_ah_loads_databus: assert property (p_ah_loads_databus);

endmodule