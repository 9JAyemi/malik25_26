module sequence_counter(
  input slowest_sync_clk,
  input lpf_int,
  output reg Core,
  output reg bsr,
  output reg pr
);

  reg [31:0] cnt_100M = 0;
  reg [7:0] cnt_core = 0;
  reg [5:0] cnt_bsr = 0;

  always @(posedge slowest_sync_clk) begin
    cnt_100M <= cnt_100M + 1;
    if (cnt_100M == 100_000_000) begin
      cnt_100M <= 0;
      Core <= 1;
    end else begin
      Core <= 0;
    end
  end

  always @(posedge lpf_int) begin
    if (Core) begin
      cnt_core <= cnt_core + 1;
      if (cnt_core == 2**8) begin
        cnt_core <= 0;
        bsr <= 1;
      end else begin
        bsr <= 0;
      end
    end else begin
      bsr <= 0;
    end
  end

  always @(posedge lpf_int) begin
    if (bsr) begin
      cnt_bsr <= cnt_bsr + 1;
      if (cnt_bsr == 2**6) begin
        cnt_bsr <= 0;
        pr <= 1;
      end else begin
        pr <= 0;
      end
    end else begin
      pr <= 0;
    end
  end

endmodule