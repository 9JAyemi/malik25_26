// SVA for module cart. Bind this file to the DUT.
// Focused, high-quality checks with key coverage.

module cart_sva(
  input  logic         clk,
  input  logic         clk7_en,
  input  logic         cpu_rst,
  input  logic         dbr,
  input  logic         ovl,
  input  logic         _cpu_as,
  input  logic         cpu_rd,
  input  logic         freeze,
  input  logic         aron,

  input  logic [23:1]  cpu_address_in,
  input  logic [31:0]  cpu_vbr,

  input  logic         sel_cart,
  input  logic         ovr,
  input  logic         sel_custom_mirror,

  input  logic [31:0]  nmi_vec_adr,
  input  logic [15:0]  nmi_adr_out,
  input  logic [15:0]  custom_mirror_q,
  input  logic [15:0]  custom_mirror_out,
  input  logic [15:0]  cart_data_out,

  input  logic         freeze_d,
  input  logic         freeze_req,

  input  logic         int7,
  input  logic         int7_req,
  input  logic         int7_ack,
  input  logic         l_int7_req,
  input  logic         l_int7_ack,
  input  logic         l_int7,
  input  logic         active
);

  // Static/comb decodes and datapath equalities
  assert property (@(posedge clk) aron);
  assert property (@(posedge clk) sel_cart == (~dbr && (cpu_address_in[23:19]==5'b1010_0)));
  assert property (@(posedge clk) ovr == (active && ~dbr && ~ovl && cpu_rd && (cpu_address_in[23:2] == nmi_vec_adr[23:2])));
  assert property (@(posedge clk) nmi_adr_out == (ovr ? (cpu_address_in[1] ? 16'h000c : 16'h00a1) : 16'h0000));
  assert property (@(posedge clk) sel_custom_mirror == (~dbr && cpu_rd && (cpu_address_in[23:12]==12'b1010_1001_1111)));
  assert property (@(posedge clk) custom_mirror_out == (sel_custom_mirror ? custom_mirror_q : 16'h0000));
  assert property (@(posedge clk) cart_data_out == (custom_mirror_out | nmi_adr_out));
  assert property (@(posedge clk) int7_ack == (&cpu_address_in && ~_cpu_as));

  // Edge-detect and requests
  assert property (@(posedge clk) freeze_req == (freeze && !freeze_d));
  assert property (@(posedge clk) int7_req == freeze_req);

  // Gated register update behavior (update on prior clk7_en, hold otherwise)
  assert property (@(posedge clk) $past(clk7_en) |-> nmi_vec_adr == ($past(cpu_vbr) + 32'h0000_007c));
  assert property (@(posedge clk) !$past(clk7_en) |-> nmi_vec_adr == $past(nmi_vec_adr));

  assert property (@(posedge clk) $past(clk7_en) |-> freeze_d == $past(freeze));
  assert property (@(posedge clk) !$past(clk7_en) |-> freeze_d == $past(freeze_d));

  assert property (@(posedge clk) $past(clk7_en) |-> l_int7_req == $past(int7_req));
  assert property (@(posedge clk) $past(clk7_en) |-> l_int7_ack == $past(int7_ack));

  assert property (@(posedge clk) $past(clk7_en) |-> int7 ==
    ($past(cpu_rst) ? 1'b0 :
      ($past(int7_req) ? 1'b1 :
        ($past(int7_ack) ? 1'b0 : $past(int7)))));

  assert property (@(posedge clk) $past(clk7_en) |-> l_int7 ==
    ($past(cpu_rst) ? 1'b0 :
      ($past(l_int7_req) ? 1'b1 :
        ($past(l_int7_ack && cpu_rd) ? 1'b0 : $past(l_int7)))));

  assert property (@(posedge clk) $past(clk7_en) |-> active ==
    ($past(cpu_rst) ? 1'b0 :
      ($past(l_int7 && l_int7_ack && cpu_rd) ? 1'b1 :
        ($past(sel_cart && cpu_rd) ? 1'b0 : $past(active)))));

  assert property (@(posedge clk) !$past(clk7_en) |-> (int7 == $past(int7)
                                                    && l_int7_req == $past(l_int7_req)
                                                    && l_int7_ack == $past(l_int7_ack)
                                                    && l_int7 == $past(l_int7)
                                                    && active == $past(active)));

  // Key functional coverage
  cover property (@(posedge clk) clk7_en && !cpu_rst ##1 freeze_req ##1 int7 ##[1:20] int7_ack ##1 !int7);
  cover property (@(posedge clk) $rose(active));
  cover property (@(posedge clk) ovr && (cpu_address_in[1]==1'b0) && (nmi_adr_out==16'h00a1));
  cover property (@(posedge clk) ovr && (cpu_address_in[1]==1'b1) && (nmi_adr_out==16'h000c));
  cover property (@(posedge clk) sel_custom_mirror && (custom_mirror_out!=16'h0000) && !ovr);
  cover property (@(posedge clk) sel_cart);
endmodule

bind cart cart_sva cart_sva_i (
  .clk               (clk),
  .clk7_en           (clk7_en),
  .cpu_rst           (cpu_rst),
  .dbr               (dbr),
  .ovl               (ovl),
  ._cpu_as           (_cpu_as),
  .cpu_rd            (cpu_rd),
  .freeze            (freeze),
  .aron              (aron),

  .cpu_address_in    (cpu_address_in),
  .cpu_vbr           (cpu_vbr),

  .sel_cart          (sel_cart),
  .ovr               (ovr),
  .sel_custom_mirror (sel_custom_mirror),

  .nmi_vec_adr       (nmi_vec_adr),
  .nmi_adr_out       (nmi_adr_out),
  .custom_mirror_q   (custom_mirror_q),
  .custom_mirror_out (custom_mirror_out),
  .cart_data_out     (cart_data_out),

  .freeze_d          (freeze_d),
  .freeze_req        (freeze_req),

  .int7              (int7),
  .int7_req          (int7_req),
  .int7_ack          (int7_ack),
  .l_int7_req        (l_int7_req),
  .l_int7_ack        (l_int7_ack),
  .l_int7            (l_int7),
  .active            (active)
);