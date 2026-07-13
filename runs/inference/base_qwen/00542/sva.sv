module my_module_sva (
    input logic clk,
    input logic rst_n,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    output logic X
);
    // Local signals
    wire and0_out;
    wire or0_out_X;
    wire pwrgood_pp0_out_X;

    // Assertions
    // A1, A2, A3, and B1 inputs should not change during the clock cycle
    property p_inputs_stable;
        @(posedge clk) disable iff (!rst_n) $stable(A1) && $stable(A2) && $stable(A3) && $stable(B1);
    endproperty
    a_inputs_stable: assert property (p_inputs_stable) else $error("Inputs A1, A2, A3, and B1 should not change during the clock cycle");

    // VPWR and VGND inputs should not change during the clock cycle
    property p_power_stable;
        @(posedge clk) disable iff (!rst_n) $stable(VPWR) && $stable(VGND);
    endproperty
    a_power_stable: assert property (p_power_stable) else $error("Inputs VPWR and VGND should not change during the clock cycle");

    // VPB and VNB inputs should not change during the clock cycle
    property p_supply_stable;
        @(posedge clk) disable iff (!rst_n) $stable(VPB) && $stable(VNB);
    endproperty
    a_supply_stable: assert property (p_supply_stable) else $error("Inputs VPB and VNB should not change during the clock cycle");

    // X output should be stable during the clock cycle
    property p_output_stable;
        @(posedge clk) disable iff (!rst_n) $stable(X);
    endproperty
    a_output_stable: assert property (p_output_stable) else $error("Output X should be stable during the clock cycle");

    // A3, A1, A2, and B1 inputs should not be high simultaneously
    property p_inputs_not_simultaneously_high;
        @(posedge clk) disable iff (!rst_n) !(A3 && A1 && A2 && B1);
    endproperty
    a_inputs_not_simultaneously_high: assert property (p_inputs_not_simultaneously_high) else $error("Inputs A3, A1, A2, and B1 should not be high simultaneously");

    // VPWR and VGND should not be high simultaneously
    property p_power_not_simultaneously_high;
        @(posedge clk) disable iff (!rst_n) !(VPWR && VGND);
    endproperty
    a_power_not_simultaneously_high: assert property (p_power_not_simultaneously_high) else $error("Inputs VPWR and VGND should not be high simultaneously");

    // VPB and VNB should not be high simultaneously
    property p_supply_not_simultaneously_high;
        @(posedge clk) disable iff (!rst_n) !(VPB && VNB);
    endproperty
    a_supply_not_simultaneously_high: assert property (p_supply_not_simultaneously_high) else $error("Inputs VPB and VNB should not be high simultaneously");

    // X output should be high when A3, A1, and A2 are high and B1 is low
    property p_output_high_when_inputs_high;
        @(posedge clk) disable iff (!rst_n) (A3 && A1 && A2 && !B1) |-> X;
    endproperty
    a_output_high_when_inputs_high: assert property (p_output_high_when_inputs_high) else $error("Output X should be high when A3, A1, and A2 are high and B1 is low");

    // X output should be low when A3, A1, and A2 are low or B1 is high
    property p_output_low_when_inputs_low_or_b1_high;
        @(posedge clk) disable iff (!rst_n) (!A3 || !A1 || !A2 || B1) |-> !X;
    endproperty
    a_output_low_when_inputs_low_or_b1_high: assert property (p_output_low_when_inputs_low_or_b1_high) else $error("Output X should be low when A3, A1, and A2 are low or B1 is high");

    // At reset, X output should be low
    property p_output_low_at_reset;
        @(posedge clk) !rst_n |-> !X;
    endproperty
    a_output_low_at_reset: assert property (p_output_low_at_reset) else $error("Output X should be low at reset");

endmodule