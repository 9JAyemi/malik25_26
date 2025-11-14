module uart_tx(
  input clk,
  input reset_n,
  input clk_en,
  input begintransfer,
  input tx_wr_strobe,
  input status_wr_strobe,
  input do_force_break,
  input [7:0] tx_data,
  input [15:0] baud_divisor,
  output tx_overrun,
  output tx_ready,
  output tx_shift_empty,
  output txd
);

  reg baud_clk_en;
  reg [15:0] baud_rate_counter;
  wire baud_rate_counter_is_zero;
  reg do_load_shifter;
  wire do_shift;
  reg pre_txd;
  wire shift_done;
  wire [9:0] tx_load_val;
  reg tx_overrun;
  reg tx_ready;
  reg tx_shift_empty;
  wire tx_shift_reg_out;
  wire [9:0] tx_shift_register_contents;
  wire tx_wr_strobe_onset;
  reg txd;
  reg [9:0] unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_out;
  wire [9:0] unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_in;

  assign tx_wr_strobe_onset = tx_wr_strobe && begintransfer;
  assign tx_load_val = {{1 {1'b1}}, tx_data, 1'b0};
  assign shift_done = ~(|tx_shift_register_contents);

  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      do_load_shifter <= 0;
    end else if (clk_en) begin
      do_load_shifter <= (~tx_ready) && shift_done;
    end
  end

  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      tx_ready <= 1'b1;
    end else if (clk_en) begin
      if (tx_wr_strobe_onset) begin
        tx_ready <= 0;
      end else if (do_load_shifter) begin
        tx_ready <= -1;
      end
    end
  end

  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      tx_overrun <= 0;
    end else if (clk_en) begin
      if (status_wr_strobe) begin
        tx_overrun <= 0;
      end else if (~tx_ready && tx_wr_strobe_onset) begin
        tx_overrun <= -1;
      end
    end
  end

  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      tx_shift_empty <= 1'b1;
    end else if (clk_en) begin
      tx_shift_empty <= tx_ready && shift_done;
    end
  end

  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      baud_rate_counter <= 0;
    end else if (clk_en) begin
      if (baud_rate_counter_is_zero || do_load_shifter) begin
        baud_rate_counter <= baud_divisor;
      end else begin
        baud_rate_counter <= baud_rate_counter - 1;
      end
    end
  end

  assign baud_rate_counter_is_zero = baud_rate_counter == 0;
  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      baud_clk_en <= 0;
    end else if (clk_en) begin
      baud_clk_en <= baud_rate_counter_is_zero;
    end
  end

  assign do_shift = baud_clk_en  && (~shift_done) && (~do_load_shifter);
  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      pre_txd <= 1;
    end else if (~shift_done) begin
      pre_txd <= tx_shift_reg_out;
    end
  end

  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      txd <= 1;
    end else if (clk_en) begin
      txd <= pre_txd & ~do_force_break;
    end
  end

  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_out <= 0;
    end else if (clk_en) begin
      unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_out <= unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_in;
    end
  end

  assign unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_in = (do_load_shifter)? tx_load_val : (do_shift)? {1'b0, unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_out[9 : 1]} : unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_out;
  assign tx_shift_register_contents = unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_out;
  assign tx_shift_reg_out = unxshiftxtx_shift_register_contentsxtx_shift_reg_outxx5_out[0];

endmodule