module limbus_cpu_cpu_nios2_oci_dtrace (
  // inputs:
  input clk,
  input [21:0] cpu_d_address,
  input cpu_d_read,
  input [31:0] cpu_d_readdata,
  input cpu_d_wait,
  input cpu_d_write,
  input [31:0] cpu_d_writedata,
  input jrst_n,
  input [15:0] trc_ctrl,

  // outputs:
  output reg [35:0] atm,
  output reg [35:0] dtm
);

  wire [31:0] cpu_d_address_0_padded;
  wire [31:0] cpu_d_readdata_0_padded;
  wire [31:0] cpu_d_writedata_0_padded;
  wire dummy_tie_off;
  wire record_load_addr;
  wire record_load_data;
  wire record_store_addr;
  wire record_store_data;
  wire [3:0] td_mode_trc_ctrl;

  assign cpu_d_writedata_0_padded = {cpu_d_writedata, 32'b0};
  assign cpu_d_readdata_0_padded = {cpu_d_readdata, 32'b0};
  assign cpu_d_address_0_padded = {cpu_d_address, 32'b0};

  //limbus_cpu_cpu_nios2_oci_trc_ctrl_td_mode, which is an e_instance
  //limbus_cpu_cpu_nios2_oci_td_mode limbus_cpu_cpu_nios2_oci_trc_ctrl_td_mode
  //  (
  //    .ctrl    (trc_ctrl[8 : 0]),
  //    .td_mode (td_mode_trc_ctrl)
  //  );

  assign {record_load_addr, record_store_addr,
         record_load_data, record_store_data} = td_mode_trc_ctrl;

  always @ (posedge clk or negedge jrst_n) begin
    if (jrst_n == 0) begin
      atm <= 0;
      dtm <= 0;
    end else begin
      if (cpu_d_read) begin
        atm <= cpu_d_address;
        dtm <= cpu_d_readdata;
      end else if (cpu_d_write) begin
        atm <= cpu_d_address;
        dtm <= cpu_d_writedata;
      end else if (cpu_d_wait) begin
        atm <= 0;
        dtm <= 0;
      end
    end
  end

  assign dummy_tie_off = cpu_d_wait | cpu_d_read | cpu_d_write;

endmodule