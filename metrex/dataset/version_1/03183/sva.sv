// SVA for bt and top
// Purely combinational, event-based sampling on input/output changes to avoid clock dependency.

module bt_sva (input [7:0] in, input [7:0] out);
  // Functional equivalence and X-propagation
  ap_func:   assert property (@(in or out) ##0 (out === ~in));
  ap_known:  assert property (@(in or out) (!$isunknown(in)) |-> ##0 (!$isunknown(out)));

  // Bit-level correlation and toggle coverage
  genvar i;
  for (i=0; i<8; i++) begin : GBIT
    ap_edge:  assert property (@(posedge in[i] or negedge in[i]) ##0 (out[i] === ~in[i]));
    cp_rise:  cover  property (@(posedge in[i]) ##0 (out[i] == 1'b0));
    cp_fall:  cover  property (@(negedge in[i]) ##0 (out[i] == 1'b1));
  end

  // Isolation: if exactly one input bit changes, only the corresponding output bit changes
  ap_onebit_iso: assert property (@(in or out)
    !$isunknown($past(in)) && !$isunknown($past(out)) &&
    $onehot(in ^ $past(in)) |-> ##0 ($onehot(out ^ $past(out)) &&
                                     ((out ^ $past(out)) == (in ^ $past(in))))
  );

  // Corner patterns
  cp_all0: cover property (@(in) in == 8'h00 && out == 8'hFF);
  cp_all1: cover property (@(in) in == 8'hFF && out == 8'h00);
endmodule

module top_sva (input [31:0] incom, input [31:0] outgo);
  // Functional equivalence and X-propagation
  ap_func32:  assert property (@(incom or outgo) ##0 (outgo === ~incom));
  ap_known32: assert property (@(incom or outgo) (!$isunknown(incom)) |-> ##0 (!$isunknown(outgo)));

  // Bit-level correlation across full bus
  genvar j;
  for (j=0; j<32; j++) begin : GBIT32
    ap_edge32: assert property (@(posedge incom[j] or negedge incom[j]) ##0 (outgo[j] === ~incom[j]));
  end

  // Byte isolation: changing only one input byte affects only that output byte
  ap_iso_b0: assert property (@(incom or outgo)
    $changed(incom[7:0])   && $stable(incom[31:8])  |-> ##0
    ($changed(outgo[7:0])  && $stable(outgo[31:8])  && (outgo[7:0]  === ~incom[7:0]))
  );
  ap_iso_b1: assert property (@(incom or outgo)
    $changed(incom[15:8])  && $stable(incom[31:16]) && $stable(incom[7:0]) |-> ##0
    ($changed(outgo[15:8]) && $stable(outgo[31:16]) && $stable(outgo[7:0]) && (outgo[15:8] === ~incom[15:8]))
  );
  ap_iso_b2: assert property (@(incom or outgo)
    $changed(incom[23:16]) && $stable(incom[31:24]) && $stable(incom[15:0]) |-> ##0
    ($changed(outgo[23:16])&& $stable(outgo[31:24]) && $stable(outgo[15:0]) && (outgo[23:16] === ~incom[23:16]))
  );
  ap_iso_b3: assert property (@(incom or outgo)
    $changed(incom[31:24]) && $stable(incom[23:0]) |-> ##0
    ($changed(outgo[31:24])&& $stable(outgo[23:0]) && (outgo[31:24] === ~incom[31:24]))
  );

  // Byte pattern coverage
  genvar k;
  for (k=0; k<4; k++) begin : GBYTE
    localparam int L = 8*k;
    cp_zero: cover property (@(incom) incom[L +: 8] == 8'h00 && outgo[L +: 8] == 8'hFF);
    cp_ones: cover property (@(incom) incom[L +: 8] == 8'hFF && outgo[L +: 8] == 8'h00);
  end
endmodule

// Bind into DUT
bind bt  bt_sva  bt_sva_b  (.in(in),   .out(out));
bind top top_sva top_sva_b (.incom(incom), .outgo(outgo));