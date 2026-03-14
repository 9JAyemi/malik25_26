module gray_converter_sva (
    input logic [3:0] binary_in,
    input logic       gray_ctrl,
    input logic       rst_n,
    input logic [3:0] gray_out
);
    // Clocks: posedge rst_n and posedge gray_ctrl. Reset is active-low (disable iff !rst_n). Logic is sequential.

    ///// rst_n-posedge pipeline updates /////
    // Next rst_n posedge: binary_reg1 captures previous binary_in.
    check_binary_reg1_captures_binary_in_on_rstn: assert property (
        @(posedge rst_n) disable iff (!rst_n)
            1'b1 |=> (binary_reg1 == $past(binary_in))
    );

    // Next rst_n posedge: binary_reg2 captures previous binary_reg1.
    check_binary_reg2_captures_binary_reg1_on_rstn: assert property (
        @(posedge rst_n) disable iff (!rst_n)
            1'b1 |=> (binary_reg2 == $past(binary_reg1))
    );

    // Next rst_n posedge: gray_reg1 captures previous gray_out.
    check_gray_reg1_captures_gray_out_on_rstn: assert property (
        @(posedge rst_n) disable iff (!rst_n)
            1'b1 |=> (gray_reg1 == $past(gray_out))
    );

    // Next rst_n posedge: gray_reg2 captures previous gray_reg1.
    check_gray_reg2_captures_gray_reg1_on_rstn: assert property (
        @(posedge rst_n) disable iff (!rst_n)
            1'b1 |=> (gray_reg2 == $past(gray_reg1))
    );

    ///// gray_ctrl-posedge gray_out update /////
    // Next gray_ctrl posedge: gray_out = prev(gray_reg1) XOR (prev(gray_reg2) << 1).
    check_gray_out_update_on_gray_ctrl: assert property (
        @(posedge gray_ctrl) disable iff (!rst_n)
            1'b1 |=> (gray_out == ($past(gray_reg1) ^ { $past(gray_reg2)[2:0], 1'b0 }))
    );

    // Next gray_ctrl posedge: gray_out[0] equals prev(gray_reg1[0]).
    check_gray_out_bit0_on_gray_ctrl: assert property (
        @(posedge gray_ctrl) disable iff (!rst_n)
            1'b1 |=> (gray_out[0] == $past(gray_reg1[0]))
    );

    // Next gray_ctrl posedge: gray_out[1] equals prev(gray_reg1[1]) XOR prev(gray_reg2[0]).
    check_gray_out_bit1_on_gray_ctrl: assert property (
        @(posedge gray_ctrl) disable iff (!rst_n)
            1'b1 |=> (gray_out[1] == ($past(gray_reg1[1]) ^ $past(gray_reg2[0])))
    );

    // Next gray_ctrl posedge: gray_out[2] equals prev(gray_reg1[2]) XOR prev(gray_reg2[1]).
    check_gray_out_bit2_on_gray_ctrl: assert property (
        @(posedge gray_ctrl) disable iff (!rst_n)
            1'b1 |=> (gray_out[2] == ($past(gray_reg1[2]) ^ $past(gray_reg2[1])))
    );

    // Next gray_ctrl posedge: gray_out[3] equals prev(gray_reg1[3]) XOR prev(gray_reg2[2]).
    check_gray_out_bit3_on_gray_ctrl: assert property (
        @(posedge gray_ctrl) disable iff (!rst_n)
            1'b1 |=> (gray_out[3] == ($past(gray_reg1[3]) ^ $past(gray_reg2[2])))
    );

endmodule