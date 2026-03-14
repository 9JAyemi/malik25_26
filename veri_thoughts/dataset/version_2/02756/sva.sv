module custom_and2_sva (
    input logic o,
    input logic i0,
    input logic i1
);
    // Output equals i0 & i1 when i0 rises.
    check_and_on_i0_posedge: assert property (
        @(posedge i0) disable iff (1'b0) o === (i0 & i1)
    );
    // Output equals i0 & i1 when i1 rises.
    check_and_on_i1_posedge: assert property (
        @(posedge i1) disable iff (1'b0) o === (i0 & i1)
    );
    // Output equals i0 & i1 when o rises.
    check_and_on_o_posedge: assert property (
        @(posedge o) disable iff (1'b0) o === (i0 & i1)
    );
    // o can only rise when both inputs are 1.
    check_o_rise_requires_inputs_high: assert property (
        @(posedge o) disable iff (1'b0) (i0 === 1'b1) && (i1 === 1'b1)
    );
endmodule