module mux_encoder_decoder_xor_sva (
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] out
);
    // For sel==000, out equals data0 XOR 1
    check_sel0_xor1_value: assert property (
        @(posedge $global_clock) (sel == 3'b000) |-> (out == (data0 ^ 4'b0001))
    );

    // For sel==001, out equals data1 XOR 2
    check_sel1_xor2_value: assert property (
        @(posedge $global_clock) (sel == 3'b001) |-> (out == (data1 ^ 4'b0010))
    );

    // For sel==010, out equals data2 XOR 4
    check_sel2_xor4_value: assert property (
        @(posedge $global_clock) (sel == 3'b010) |-> (out == (data2 ^ 4'b0100))
    );

    // For sel==011, out equals data3 XOR 8
    check_sel3_xor8_value: assert property (
        @(posedge $global_clock) (sel == 3'b011) |-> (out == (data3 ^ 4'b1000))
    );

    // For any sel with MSB=1 (100..111), out passes data4 unchanged
    check_sel_highbit_uses_data4: assert property (
        @(posedge $global_clock) (sel[2] == 1'b1) |-> (out == data4)
    );

    // If sel stays 000 and data0 is stable, out remains stable
    stability_sel0_data0_stable: assert property (
        @(posedge $global_clock) (sel == 3'b000 && $past(sel) == 3'b000 && $stable(data0)) |-> (out == $past(out))
    );

    // If sel stays 001 and data1 is stable, out remains stable
    stability_sel1_data1_stable: assert property (
        @(posedge $global_clock) (sel == 3'b001 && $past(sel) == 3'b001 && $stable(data1)) |-> (out == $past(out))
    );

    // If sel stays 010 and data2 is stable, out remains stable
    stability_sel2_data2_stable: assert property (
        @(posedge $global_clock) (sel == 3'b010 && $past(sel) == 3'b010 && $stable(data2)) |-> (out == $past(out))
    );

    // If sel stays 011 and data3 is stable, out remains stable
    stability_sel3_data3_stable: assert property (
        @(posedge $global_clock) (sel == 3'b011 && $past(sel) == 3'b011 && $stable(data3)) |-> (out == $past(out))
    );

    // If sel MSB stays 1 and data4 is stable, out remains stable
    stability_sel_highbit_data4_stable: assert property (
        @(posedge $global_clock) (sel[2] && $past(sel[2]) && $stable(data4)) |-> (out == $past(out))
    );

endmodule