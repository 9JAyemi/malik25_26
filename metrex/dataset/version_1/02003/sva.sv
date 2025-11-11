// SVA for priority_encoder and mux_4to1_priority_encoder
// Bind these into the DUTs

module priority_encoder_sva(input logic [7:0] a,b,c,d, input logic [1:0] index);

  function automatic logic [1:0] pri_idx(input logic [7:0] a,b,c,d);
    if (a!=8'h00) pri_idx = 2'b00;
    else if (b!=8'h00) pri_idx = 2'b01;
    else if (c!=8'h00) pri_idx = 2'b10;
    else               pri_idx = 2'b11;
  endfunction

  default clocking cb @(*); endclocking

  // Correctness (priority and all-zero behavior)
  ap_idx: assert property (disable iff ($isunknown({a,b,c,d,index}))
                           index == pri_idx(a,b,c,d));

  // Coverage of key cases (including priority override)
  cp_a:         cover property (! $isunknown({a,b,c,d}) && (a!=8'h00));
  cp_b:         cover property (! $isunknown({a,b,c,d}) && (a==8'h00) && (b!=8'h00));
  cp_c:         cover property (! $isunknown({a,b,c,d}) && (a==8'h00) && (b==8'h00) && (c!=8'h00));
  cp_d_only:    cover property (! $isunknown({a,b,c,d}) && (a==8'h00) && (b==8'h00) && (c==8'h00) && (d!=8'h00));
  cp_all_zero:  cover property (! $isunknown({a,b,c,d}) && ({a,b,c,d}==32'h0));
  cp_a_wins:    cover property (! $isunknown({a,b,c,d}) && (a!=8'h00) && ((b!=8'h00)||(c!=8'h00)||(d!=8'h00)));

endmodule


module mux_4to1_priority_encoder_sva(input logic [7:0] a,b,c,d,
                                      input logic [1:0] select,
                                      input logic [7:0] out);

  default clocking cb @(*); endclocking

  // Functional correctness per select
  ap_sel0: assert property (disable iff ($isunknown({select,a})) (select==2'b00) |-> (out==a));
  ap_sel1: assert property (disable iff ($isunknown({select,b})) (select==2'b01) |-> (out==b));
  ap_sel2: assert property (disable iff ($isunknown({select,c})) (select==2'b10) |-> (out==c));
  ap_sel3: assert property (disable iff ($isunknown({select,d})) (select==2'b11) |-> (out==d));

  // Coverage: hit each select
  cv_sel0: cover property (! $isunknown(select) && select==2'b00);
  cv_sel1: cover property (! $isunknown(select) && select==2'b01);
  cv_sel2: cover property (! $isunknown(select) && select==2'b10);
  cv_sel3: cover property (! $isunknown(select) && select==2'b11);

endmodule


// Bind to DUTs
bind priority_encoder          priority_encoder_sva          pe_sva(.a(a), .b(b), .c(c), .d(d), .index(index));
bind mux_4to1_priority_encoder mux_4to1_priority_encoder_sva m_sva(.a(a), .b(b), .c(c), .d(d), .select(select), .out(out));