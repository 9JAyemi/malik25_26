module WB_intercon_sva (
    input logic master_STB,
    input logic master_WE,
    input logic [31:0] master_DAT_I,
    input logic [31:0] master_ADDR,
    input logic [511:0] slave_DAT_I,
    input logic [15:0] slave_ACK,
    input logic [31:0] master_DAT_O,
    input logic [31:0] slave_DAT_O,
    input logic [31:0] slave_ADDR,
    input logic [15:0] slave_STB,
    input logic master_ACK,
    input logic slave_WE
);
    ///// Combinational mapping checks sampled on master_STB edge /////
    // master_ACK equals the selected slave_ACK bit indexed by master_ADDR[31:28].
    check_master_ack_select: assert property (
        @(posedge master_STB) master_ACK == slave_ACK[master_ADDR[31:28]]
    );
    // master_DAT_O equals the 32-bit slice of slave_DAT_I selected by master_ADDR[31:28].
    check_master_data_mux_select: assert property (
        @(posedge master_STB) master_DAT_O == slave_DAT_I[(master_ADDR[31:28] << 5) +: 32]
    );
    // slave_ADDR is {4'b0, master_ADDR[27:0]}.
    check_slave_addr_map: assert property (
        @(posedge master_STB) slave_ADDR == {4'b0, master_ADDR[27:0]}
    );
    // slave_DAT_O passes through master_DAT_I.
    check_slave_dat_o_passthrough: assert property (
        @(posedge master_STB) slave_DAT_O == master_DAT_I
    );
    // slave_WE passes through master_WE.
    check_slave_we_passthrough: assert property (
        @(posedge master_STB) slave_WE == master_WE
    );
    // slave_STB equals one-hot of selected index when master_STB=1, else zero.
    check_slave_stb_exact_pattern: assert property (
        @(posedge master_STB) slave_STB == (master_STB ? (16'h1 << master_ADDR[31:28]) : 16'h0)
    );
    // The selected slave_STB bit equals master_STB.
    check_slave_stb_selected_bit: assert property (
        @(posedge master_STB) slave_STB[master_ADDR[31:28]] == master_STB
    );
    // All unselected slave_STB bits are zero.
    check_slave_stb_unselected_zero: assert property (
        @(posedge master_STB) (slave_STB & ~(16'h1 << master_ADDR[31:28])) == 16'h0
    );
    // When master_STB is asserted, slave_STB is one-hot.
    check_slave_stb_onehot_when_asserted: assert property (
        @(posedge master_STB) $onehot(slave_STB)
    );
endmodule