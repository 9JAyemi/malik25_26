
module niosii_nios2_gen2_0_cpu_nios2_oci_dtrace (
  // inputs:
  clk,
  cpu_d_address,
  cpu_d_read,
  cpu_d_readdata,
  cpu_d_wait,
  cpu_d_write,
  cpu_d_writedata,
  jrst_n,
  trc_ctrl,
  // outputs:
  atm,
  dtm
);

  output [31:0] atm;
  output [31:0] dtm;
  input clk;
  input [22:0] cpu_d_address;
  input cpu_d_read;
  input [31:0] cpu_d_readdata;
  input cpu_d_wait;
  input cpu_d_write;
  input [31:0] cpu_d_writedata;
  input jrst_n;
  input [15:0] trc_ctrl;

  reg [31:0] atm;
  reg [31:0] dtm;

  wire [31:0] cpu_d_address_0_padded;
  wire [31:0] cpu_d_readdata_0_padded;
  wire [31:0] cpu_d_writedata_0_padded;
  wire dummy_tie_off;
  wire record_load_addr;
  wire record_load_data;
  wire record_store_addr;
  wire record_store_data;
  wire [3:0] td_mode_trc_ctrl;

  assign cpu_d_writedata_0_padded = {7'b0, cpu_d_writedata};
  assign cpu_d_readdata_0_padded = {7'b0, cpu_d_readdata};
  assign cpu_d_address_0_padded = {7'b0, cpu_d_address[22:0]};

  niosii_nios2_gen2_0_cpu_nios2_oci_td_mode niosii_nios2_gen2_0_cpu_nios2_oci_trc_ctrl_td_mode_inst  (
    .ctrl(trc_ctrl),
    .td_mode(td_mode_trc_ctrl)
  );

  assign {record_load_addr, record_store_addr, record_load_data, record_store_data} = td_mode_trc_ctrl;

  always @(posedge clk or negedge jrst_n) begin
    if (jrst_n == 0) begin
      atm <= 0;
      dtm <= 0;
    end
    else begin
      if (cpu_d_wait == 0) begin
        if (cpu_d_read == 1) begin
          if (record_load_addr) begin
            atm <= cpu_d_address_0_padded[31:0];
          end
          if (record_load_data) begin
            dtm <= cpu_d_readdata_0_padded[31:0];
          end
        end
        else if (cpu_d_write == 1) begin
          if (record_store_addr) begin
            atm <= cpu_d_address_0_padded[31:0];
          end
          if (record_store_data) begin
            dtm <= cpu_d_writedata_0_padded[31:0];
          end
        end
      end
    end
  end

  assign dummy_tie_off = cpu_d_wait | cpu_d_read | cpu_d_write;

endmodule
module niosii_nios2_gen2_0_cpu_nios2_oci_td_mode (
  ctrl,
  td_mode
);

  input  [15:0] ctrl;
  output [3:0] td_mode;

  assign td_mode = ctrl[3:0];

endmodule