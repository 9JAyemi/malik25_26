// SVA for j1_peripheral_mux
module j1_peripheral_mux_sva (
  input  logic        sys_clk_i,
  input  logic        sys_rst_i,
  input  logic        j1_io_rd,
  input  logic        j1_io_wr,
  input  logic [15:0] j1_io_addr,
  input  logic [15:0] j1_io_din,
  input  logic [7:0]  cs,
  input  logic [15:0] mult_dout,
  input  logic [15:0] div_dout,
  input  logic        uart_dout,
  input  logic [15:0] dp_ram_dout,
  input  logic [15:0] bt_dout,
  input  logic [15:0] audio_dout,
  input  logic [15:0] ultra_dout,
  input  logic        echo
);

  default clocking cb @(posedge sys_clk_i); endclocking
  default disable iff (sys_rst_i);

  function automatic logic [7:0] exp_cs(input logic [7:0] hi);
    unique case (hi)
      8'h63: exp_cs = 8'b1000_0000;
      8'h64: exp_cs = 8'b0100_0000;
      8'h65: exp_cs = 8'b0010_0000;
      8'h66: exp_cs = 8'b0001_0000;
      8'h67: exp_cs = 8'b0000_1000;
      8'h68: exp_cs = 8'b0000_0100;
      8'h69: exp_cs = 8'b0000_0010;
      8'h70: exp_cs = 8'b0000_0001;
      default: exp_cs = 8'b0000_0000;
    endcase
  endfunction

  // Decoder correctness and onehot-0
  assert property (cs == exp_cs(j1_io_addr[15:8]));
  assert property ($onehot0(cs));

  // Mux correctness per select
  assert property ((cs == 8'b1000_0000) |-> (j1_io_din === audio_dout)); // altavoz
  assert property ((cs == 8'b0100_0000) |-> (j1_io_din === ultra_dout)); // ultra
  assert property ((cs == 8'b0010_0000) |-> (j1_io_din === audio_dout)); // audio
  assert property ((cs == 8'b0001_0000) |-> (j1_io_din === bt_dout));    // bt
  assert property ((cs == 8'b0000_1000) |-> (j1_io_din === mult_dout));  // mult
  assert property ((cs == 8'b0000_0100) |-> (j1_io_din === div_dout));   // div
  // UART: ensure proper zero-extension and LSB match
  assert property ((cs == 8'b0000_0010) |-> (j1_io_din[15:1] == '0 && j1_io_din[0] == uart_dout));
  assert property ((cs == 8'b0000_0001) |-> (j1_io_din === dp_ram_dout)); // dp_ram
  assert property ((cs == 8'b0000_0000) |-> (j1_io_din == 16'h0000));     // default

  // Outputs independent of unused inputs (rd, wr, echo)
  assert property (
    $stable({j1_io_addr, mult_dout, div_dout, dp_ram_dout, bt_dout, audio_dout, ultra_dout, uart_dout}) &&
    !$stable({j1_io_rd, j1_io_wr, echo})
    |-> (cs == $past(cs) && j1_io_din === $past(j1_io_din))
  );

  // Coverage: hit each select and default; UART both data values
  cover property (cs == 8'b1000_0000);
  cover property (cs == 8'b0100_0000);
  cover property (cs == 8'b0010_0000);
  cover property (cs == 8'b0001_0000);
  cover property (cs == 8'b0000_1000);
  cover property (cs == 8'b0000_0100);
  cover property (cs == 8'b0000_0010);
  cover property (cs == 8'b0000_0001);
  cover property (cs == 8'b0000_0000);
  cover property (cs == 8'b0000_0010 && j1_io_din[15:1] == '0 && j1_io_din[0] == 1'b0);
  cover property (cs == 8'b0000_0010 && j1_io_din[15:1] == '0 && j1_io_din[0] == 1'b1);

endmodule

bind j1_peripheral_mux j1_peripheral_mux_sva sva_i (.*);