// SVA checker for bt_receiver
module bt_receiver_sva #(
  parameter int n = 8,
  parameter int m = 8,
  parameter int baud_rate = 9600
);
  localparam int BAUD_DIV = (50_000_000 / baud_rate) - 1;

  default clocking cb @(posedge clk); endclocking

  initial begin
    assert (BAUD_DIV > 0) else $error("BAUD_DIV must be > 0, got %0d", BAUD_DIV);
    assert (n > 0 && m > 0) else $error("n and m must be > 0");
  end

  // Asynchronous reset effect checked synchronously
  assert property (@(posedge clk) reset |-> (counter == 0 && rx_en == 0 && data_out == '0));

  default disable iff (reset);

  // No X on key state/outputs
  assert property (!$isunknown({counter, rx_en, data_out}));

  // Counter bounds
  assert property (counter inside {[0:BAUD_DIV]});

  // Counter sequencing
  assert property ((counter == 0) |=> (counter == BAUD_DIV));
  assert property ((counter > 0) |=> (counter == $past(counter) - 1));
  assert property ($changed(counter) |-> ((counter == BAUD_DIV && $past(counter) == 0) || (counter == $past(counter) - 1)));

  // Progress: from reload back to zero within BAUD_DIV cycles
  assert property ((counter == BAUD_DIV) |-> ##[1:BAUD_DIV] (counter == 0));

  // rx_en behavior
  assert property ((counter == 0) |-> rx_en);
  assert property ($rose(rx_en) |-> (counter == 0));

  // data_out updates only on reload and has expected value
  assert property ((counter != 0) |=> $stable(data_out));
  generate
    if (m <= n) begin
      assert property ((counter == 0) |=> data_out == $past(data_reg[m-1:0]));
    end else begin
      assert property ((counter == 0) |=> data_out == {{(m-n){1'b0}}, $past(data_reg)});
    end
  endgenerate

  // data_reg behavior on reload (reflects current DUT code)
  assert property ((counter == 0) |=> data_reg == ($past(data_reg) >> 1));

  // Coverage
  cover property ((counter == 0) ##1 (counter == BAUD_DIV) ##[1:BAUD_DIV] (counter == 0));
  cover property ($rose(rx_en));
  cover property ((counter == 3) ##1 (counter == 2) ##1 (counter == 1) ##1 (counter == 0));
endmodule

bind bt_receiver bt_receiver_sva #(.n(n), .m(m), .baud_rate(baud_rate)) u_bt_receiver_sva();