
module altpcierd_icm_sideband (
                   clk, rstn, 
                   cfg_busdev,  cfg_devcsr,  cfg_linkcsr, cfg_msicsr, cfg_prmcsr,
                   cfg_tcvcmap,  app_int_sts,  app_int_sts_ack, pex_msi_num, cpl_err,
                   cpl_pending,
                   cfg_busdev_del,  cfg_devcsr_del,  cfg_linkcsr_del, cfg_msicsr_del, cfg_prmcsr_del,
                   cfg_tcvcmap_del,  app_int_sts_del,  app_int_sts_ack_del, pex_msi_num_del, cpl_err_del,
                   cpl_pending_del
                   );


   input             clk;  
   input             rstn;     
   input    [ 12: 0] cfg_busdev;         input    [ 31: 0] cfg_devcsr;         input    [ 31: 0] cfg_linkcsr;        input    [ 31: 0] cfg_prmcsr;        input    [ 23: 0] cfg_tcvcmap;        input    [15:0]   cfg_msicsr;         input    [  4: 0] pex_msi_num;        input             app_int_sts;        input             app_int_sts_ack;    input    [  2: 0] cpl_err;
   input             cpl_pending;
   

   output    [ 12: 0] cfg_busdev_del;
   output    [ 31: 0] cfg_devcsr_del;
   output    [ 31: 0] cfg_linkcsr_del;
   output    [ 31: 0] cfg_prmcsr_del;
   output    [ 23: 0] cfg_tcvcmap_del;  
   output    [15:0]   cfg_msicsr_del;
   output             app_int_sts_del;
   output             app_int_sts_ack_del;  output    [  4: 0] pex_msi_num_del; 
   output    [  2: 0] cpl_err_del;
   output             cpl_pending_del;
   
   
   reg       [ 12: 0] cfg_busdev_del;
   reg       [ 31: 0] cfg_devcsr_del;
   reg       [ 31: 0] cfg_linkcsr_del;
   reg       [ 31: 0] cfg_prmcsr_del;
   reg       [ 23: 0] cfg_tcvcmap_del;   
   reg                app_int_sts_del;
   reg                app_int_sts_ack_del;
   reg       [  4: 0] pex_msi_num_del;  
   reg       [  2: 0] cpl_err_del;
   
   reg      [15:0]   cfg_msicsr_del;
   
   reg                cpl_pending_del;
  
  always @ (posedge clk or negedge rstn) begin
      if (~rstn) begin
          cfg_busdev_del      <= 13'h0;
          cfg_devcsr_del      <= 32'h0;
          cfg_linkcsr_del     <= 32'h0;
          cfg_prmcsr_del     <= 32'h0;
          cfg_tcvcmap_del     <= 24'h0;
          cfg_msicsr_del      <= 16'h0;
          app_int_sts_del     <= 1'b0;
          app_int_sts_ack_del <= 1'b0;
          pex_msi_num_del     <= 5'h0; 
          cpl_err_del         <= 3'h0; 
          cpl_pending_del     <= 1'b0;
      end
      else begin
          cfg_busdev_del      <= cfg_busdev;
          cfg_devcsr_del      <= cfg_devcsr;
          cfg_linkcsr_del     <= cfg_linkcsr;
          cfg_prmcsr_del     <= cfg_prmcsr;
          cfg_tcvcmap_del     <= cfg_tcvcmap;
          cfg_msicsr_del      <= cfg_msicsr;
          app_int_sts_del     <= app_int_sts;  app_int_sts_ack_del <= app_int_sts_ack;  
          pex_msi_num_del     <= pex_msi_num;  cpl_err_del         <= cpl_err;      cpl_pending_del     <= cpl_pending;  end
  end
endmodule
