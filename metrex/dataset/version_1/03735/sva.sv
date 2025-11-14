// Bind this SVA module to the DUT:
// bind du du_sva u_du_sva();

module du_sva (du d);

  default clocking cb @(posedge d.clk); endclocking
  default disable iff (!d.rst);

  // -------------------------
  // Asynchronous reset effect (sampled on clk)
  // -------------------------
  assert property (!d.rst |-> d.Rdeposit==0 && d.Rselect==0 && d.Rprice==0 &&
                             d.Adeposit==0 && d.purchase==0 && d.product==0 &&
                             d.change==0 && d.refund==0);

  // -------------------------
  // Register file: load/clear and priority
  // -------------------------
  // Rdeposit
  assert property (d.ldRdeposit |=> d.Rdeposit == $past(d.deposit));
  assert property (!d.ldRdeposit && d.clrRdeposit |=> d.Rdeposit == 10'd0);
  assert property (d.ldRdeposit && d.clrRdeposit |=> d.Rdeposit == $past(d.deposit)); // ld wins

  // Rselect
  assert property (d.ldRselect |=> d.Rselect == $past(d.select));
  assert property (!d.ldRselect && d.clrRselect |=> d.Rselect == 5'd0);
  assert property (d.ldRselect && d.clrRselect |=> d.Rselect == $past(d.select)); // ld wins

  // Rprice
  assert property (d.ldRprice |=> d.Rprice == $past(d.price));
  assert property (!d.ldRprice && d.clrRprice |=> d.Rprice == 10'd0);
  assert property (d.ldRprice && d.clrRprice |=> d.Rprice == $past(d.price)); // ld wins

  // -------------------------
  // Accumulator (Adeposit) and refund behavior
  // -------------------------
  // Functional relationship for refund (combinational in DUT, sampled on clk)
  assert property (d.refund == (d.Adeposit > 10'd500));

  // Update sequencing and priority: ldA > clrA > refund
  assert property (d.ldA |=> d.Adeposit == $past(d.Adeposit) + $past(d.Rdeposit));
  assert property (!d.ldA && d.clrA |=> d.Adeposit == 10'd0);
  assert property (!d.ldA && !d.clrA && d.refund |=> d.Adeposit == $past(d.Adeposit) - $past(d.Rdeposit));
  // Safety: no underflow on refund path
  assert property (!d.ldA && !d.clrA && d.refund |-> $past(d.Adeposit) >= $past(d.Rdeposit));

  // -------------------------
  // Availability/ready bit in memory (bit 15)
  // Intended invariant: ready == (qty>0 && Adeposit>=price)
  // -------------------------
  genvar i;
  generate
    for (i=0; i<32; i++) begin : g_mem_ready_chk
      assert property (d.mem[i][15] == ((d.mem[i][13:10] > 4'd0) && (d.Adeposit >= d.mem[i][9:0])));
    end
  endgenerate

  // -------------------------
  // Purchase output behavior
  // -------------------------
  assert property (d.ldRpurchase |=> d.purchase == $past(d.mem[$past(d.Rselect)][15]));
  assert property (!d.ldRpurchase && d.clrRpurchase |=> d.purchase == 1'b0);
  assert property (!d.ldRpurchase && !d.clrRpurchase |=> d.purchase == $past(d.purchase));

  // -------------------------
  // Change computation
  // -------------------------
  assert property (d.ldRchange |=> d.change == $past(d.Adeposit) - $past(d.mem[$past(d.Rselect)][9:0]));
  // Precondition to avoid underflow: only compute change when ready permits purchase
  assert property (d.ldRchange |-> $past(d.mem[$past(d.Rselect)][15]));
  assert property (!d.ldRchange && d.clrRchange |=> d.change == 10'd0);

  // -------------------------
  // Product output
  // -------------------------
  assert property (d.ldRproduct |=> d.product == $past(d.Rselect));
  assert property (!d.ldRproduct && d.clrRproduct |=> d.product == 5'd0);

  // -------------------------
  // Memory updates (price and quantity)
  // -------------------------
  // Price write
  assert property (d.ldMprice |=> d.mem[$past(d.Rselect)][9:0] == $past(d.Rprice));

  // Quantity decrement: must not go below zero and decrements by 1
  assert property (d.ldMquantity |-> $past(d.mem[$past(d.Rselect)][13:10]) > 0);
  assert property (d.ldMquantity |=> d.mem[$past(d.Rselect)][13:10] ==
                                  $past(d.mem[$past(d.Rselect)][13:10]) - 1'b1);

  // -------------------------
  // Key covers (sanity and reachability)
  // -------------------------
  cover property (d.ldRdeposit ##1 d.ldA ##1 d.ldRpurchase && $past(d.mem[$past(d.Rselect)][15]));
  cover property (d.refund);
  cover property (d.ldMprice);
  cover property (d.ldMquantity);
  cover property (d.ldRchange);

endmodule