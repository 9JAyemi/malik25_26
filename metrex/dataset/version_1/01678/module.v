
module decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_proc_sys_reset (
    input slowest_sync_clk,
    input ext_reset_in,
    input aux_reset_in,
    input mb_debug_sys_rst,
    input dcm_locked,
    output mb_reset,
    output [0:0]bus_struct_reset,
    output [0:0]peripheral_reset,
    output [0:0]interconnect_aresetn,
    output [0:0]peripheral_aresetn
);

    reg mb_reset_reg = 1'b1;

    assign bus_struct_reset = ext_reset_in | mb_debug_sys_rst;
    assign peripheral_reset = aux_reset_in | mb_debug_sys_rst;
    assign interconnect_aresetn = ~mb_debug_sys_rst;
    assign peripheral_aresetn = ~mb_debug_sys_rst;

    always @(posedge slowest_sync_clk) begin
        if (dcm_locked == 1'b1) begin
            if (mb_debug_sys_rst == 1'b1) begin
                mb_reset_reg <= 1'b0;
            end else begin
                mb_reset_reg <= 1'b1;
            end
        end
    end

    assign mb_reset = mb_reset_reg;

endmodule
