module altpcierd_icm_sideband_sva (
    input logic         clk,
    input logic         rstn,
    input logic [12:0]  cfg_busdev,
    input logic [31:0]  cfg_devcsr,
    input logic [31:0]  cfg_linkcsr,
    input logic [15:0]  cfg_msicsr,
    input logic [31:0]  cfg_prmcsr,
    input logic [23:0]  cfg_tcvcmap,
    input logic         app_int_sts,
    input logic         app_int_sts_ack,
    input logic [4:0]   pex_msi_num,
    input logic [2:0]   cpl_err,
    input logic         cpl_pending,
    input logic [12:0]  cfg_busdev_del,
    input logic [31:0]  cfg_devcsr_del,
    input logic [31:0]  cfg_linkcsr_del,
    input logic [15:0]  cfg_msicsr_del,
    input logic [31:0]  cfg_prmcsr_del,
    input logic [23:0]  cfg_tcvcmap_del,
    input logic         app_int_sts_del,
    input logic         app_int_sts_ack_del,
    input logic [4:0]   pex_msi_num_del,
    input logic [2:0]   cpl_err_del,
    input logic         cpl_pending_del
);

    // A sampled reset low clears all delayed outputs by the next clock.
    check_outputs_cleared_by_reset: assert property (
        @(posedge clk)
        !rstn |=> ({cfg_busdev_del,
                    cfg_devcsr_del,
                    cfg_linkcsr_del,
                    cfg_msicsr_del,
                    cfg_prmcsr_del,
                    cfg_tcvcmap_del,
                    app_int_sts_del,
                    app_int_sts_ack_del,
                    pex_msi_num_del,
                    cpl_err_del,
                    cpl_pending_del} == 160'h0)
    );

    // cfg_busdev_del is the registered copy of cfg_busdev.
    check_cfg_busdev_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (cfg_busdev_del == $past(cfg_busdev))
    );

    // cfg_devcsr_del is the registered copy of cfg_devcsr.
    check_cfg_devcsr_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (cfg_devcsr_del == $past(cfg_devcsr))
    );

    // cfg_linkcsr_del is the registered copy of cfg_linkcsr.
    check_cfg_linkcsr_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (cfg_linkcsr_del == $past(cfg_linkcsr))
    );

    // cfg_msicsr_del is the registered copy of cfg_msicsr.
    check_cfg_msicsr_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (cfg_msicsr_del == $past(cfg_msicsr))
    );

    // cfg_prmcsr_del is the registered copy of cfg_prmcsr.
    check_cfg_prmcsr_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (cfg_prmcsr_del == $past(cfg_prmcsr))
    );

    // cfg_tcvcmap_del is the registered copy of cfg_tcvcmap.
    check_cfg_tcvcmap_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (cfg_tcvcmap_del == $past(cfg_tcvcmap))
    );

    // app_int_sts_del is the registered copy of app_int_sts.
    check_app_int_sts_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (app_int_sts_del == $past(app_int_sts))
    );

    // app_int_sts_ack_del is the registered copy of app_int_sts_ack.
    check_app_int_sts_ack_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (app_int_sts_ack_del == $past(app_int_sts_ack))
    );

    // pex_msi_num_del is the registered copy of pex_msi_num.
    check_pex_msi_num_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (pex_msi_num_del == $past(pex_msi_num))
    );

    // cpl_err_del is the registered copy of cpl_err.
    check_cpl_err_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (cpl_err_del == $past(cpl_err))
    );

    // cpl_pending_del is the registered copy of cpl_pending.
    check_cpl_pending_delay: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (cpl_pending_del == $past(cpl_pending))
    );

endmodule