module xor_gate_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic XOR_output
);

    // Output matches the RTL XOR function after output changes and on isolated power-pin changes.
    check_xor_relation: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or posedge VNB or negedge VNB or
          posedge XOR_output or negedge XOR_output)
        (
            $changed(XOR_output) ||
            (($changed(VPWR) || $changed(VGND)) && $stable({VPB, VNB}))
        )
        |-> (XOR_output === (VPB ^ VNB))
    );

    // Equal known inputs drive the XOR output low.
    check_equal_known_inputs_drive_low: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or posedge VNB or negedge VNB or
          posedge XOR_output or negedge XOR_output)
        (
            $changed(XOR_output) ||
            (($changed(VPWR) || $changed(VGND)) && $stable({VPB, VNB}))
        ) &&
        (
            ((VPB === 1'b0) && (VNB === 1'b0)) ||
            ((VPB === 1'b1) && (VNB === 1'b1))
        )
        |-> (XOR_output === 1'b0)
    );

    // Different known inputs drive the XOR output high.
    check_different_known_inputs_drive_high: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or posedge VNB or negedge VNB or
          posedge XOR_output or negedge XOR_output)
        (
            $changed(XOR_output) ||
            (($changed(VPWR) || $changed(VGND)) && $stable({VPB, VNB}))
        ) &&
        (
            ((VPB === 1'b0) && (VNB === 1'b1)) ||
            ((VPB === 1'b1) && (VNB === 1'b0))
        )
        |-> (XOR_output === 1'b1)
    );

    // Known binary inputs produce a known binary output.
    check_known_inputs_produce_known_output: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or posedge VNB or negedge VNB or
          posedge XOR_output or negedge XOR_output)
        (
            $changed(XOR_output) ||
            (($changed(VPWR) || $changed(VGND)) && $stable({VPB, VNB}))
        ) &&
        ((VPB === 1'b0) || (VPB === 1'b1)) &&
        ((VNB === 1'b0) || (VNB === 1'b1))
        |-> ((XOR_output === 1'b0) || (XOR_output === 1'b1))
    );

    // VPWR and VGND changes alone do not change the output.
    check_power_pin_changes_do_not_toggle_output: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or posedge VNB or negedge VNB or
          posedge XOR_output or negedge XOR_output)
        (($changed(VPWR) || $changed(VGND)) && $stable({VPB, VNB}))
        |-> $stable(XOR_output)
    );

endmodule