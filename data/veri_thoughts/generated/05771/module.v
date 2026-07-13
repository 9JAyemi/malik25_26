
module nios_nios2_gen2_0_cpu_nios2_oci_dbrk (
  // inputs:
  E_st_data,
  av_ld_data_aligned_filtered,
  clk,
  d_address,
  d_read,
  d_waitrequest,
  d_write,
  debugack,
  reset_n,

  // outputs:
  cpu_d_address,
  cpu_d_read,
  cpu_d_readdata,
  cpu_d_wait,
  cpu_d_write,
  cpu_d_writedata,
  dbrk_break,
  dbrk_goto0,
  dbrk_goto1,
  dbrk_traceme,
  dbrk_traceoff,
  dbrk_traceon,
  dbrk_trigout
) ;

  output  [ 28: 0] cpu_d_address;
  output           cpu_d_read;
  output  [ 31: 0] cpu_d_readdata;
  output           cpu_d_wait;
  output           cpu_d_write;
  output  [ 31: 0] cpu_d_writedata;
  output           dbrk_break;
  output           dbrk_goto0;
  output           dbrk_goto1;
  output           dbrk_traceme;
  output           dbrk_traceoff;
  output           dbrk_traceon;
  output           dbrk_trigout;
  input   [ 31: 0] E_st_data;
  input   [ 31: 0] av_ld_data_aligned_filtered;
  input            clk;
  input   [ 28: 0] d_address;
  input            d_read;
  input            d_waitrequest;
  input            d_write;
  input            debugack;
  input            reset_n;

  reg              dbrk_break;
  reg              dbrk_goto0;
  reg              dbrk_goto1;
  reg              dbrk_traceme;
  reg              dbrk_traceoff;
  reg              dbrk_traceon;
  reg              dbrk_trigout;

  assign cpu_d_address = d_address;
  assign cpu_d_readdata = av_ld_data_aligned_filtered;
  assign cpu_d_read = d_read;
  assign cpu_d_writedata = E_st_data;
  assign cpu_d_write = d_write;
  assign cpu_d_wait = d_waitrequest;

  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      dbrk_break <= 0;
      dbrk_goto0 <= 0;
      dbrk_goto1 <= 0;
      dbrk_traceme <= 0;
      dbrk_traceoff <= 0;
      dbrk_traceon <= 0;
      dbrk_trigout <= 0;
    end else begin
      dbrk_break <= debugack;
      dbrk_goto0 <= 0;
      dbrk_goto1 <= 0;
      dbrk_traceme <= 0;
      dbrk_traceoff <= 0;
      dbrk_traceon <= 0;
      dbrk_trigout <= 0;
    end
  end

endmodule