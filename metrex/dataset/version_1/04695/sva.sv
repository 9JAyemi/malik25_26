// SVA checker for blockmem_rw32_r128
module blockmem_rw32_r128_sva (
  input  logic          clk,

  input  logic          api_we,
  input  logic [7:0]    api_addr,
  input  logic [31:0]   api_wr_data,
  input  logic [31:0]   api_rd_data,

  input  logic [4:0]    internal_addr,
  input  logic [255:0]  internal_rd_data,

  // internal regs exposed for checking
  input  logic [31:0]   mem0_api_rd_data,
  input  logic [31:0]   mem1_api_rd_data,
  input  logic [31:0]   mem2_api_rd_data,
  input  logic [31:0]   mem3_api_rd_data,
  input  logic [31:0]   mem4_api_rd_data,
  input  logic [31:0]   mem5_api_rd_data,
  input  logic [31:0]   mem6_api_rd_data,
  input  logic [31:0]   mem7_api_rd_data,

  input  logic [31:0]   mem0_int_rd_data,
  input  logic [31:0]   mem1_int_rd_data,
  input  logic [31:0]   mem2_int_rd_data,
  input  logic [31:0]   mem3_int_rd_data,
  input  logic [31:0]   mem4_int_rd_data,
  input  logic [31:0]   mem5_int_rd_data,
  input  logic [31:0]   mem6_int_rd_data,
  input  logic [31:0]   mem7_int_rd_data,

  input  logic          mem0_we,
  input  logic          mem1_we,
  input  logic          mem2_we,
  input  logic          mem3_we,
  input  logic          mem4_we,
  input  logic          mem5_we,
  input  logic          mem6_we,
  input  logic          mem7_we,

  // memories
  input  logic [31:0]   mem0 [0:31],
  input  logic [31:0]   mem1 [0:31],
  input  logic [31:0]   mem2 [0:31],
  input  logic [31:0]   mem3 [0:31],
  input  logic [31:0]   mem4 [0:31],
  input  logic [31:0]   mem5 [0:31],
  input  logic [31:0]   mem6 [0:31],
  input  logic [31:0]   mem7 [0:31]
);

  wire [7:0] we_vec = {mem7_we,mem6_we,mem5_we,mem4_we,mem3_we,mem2_we,mem1_we,mem0_we};
  wire [7:0] sel_oh = 8'b1 << api_addr[2:0];

  // Decoder correctness
  assert property (@(posedge clk) !api_we |-> (we_vec == 8'b0));
  assert property (@(posedge clk)  api_we |-> ($onehot(we_vec) && (we_vec == sel_oh)));

  // Mux correctness (API read data selects proper bank register)
  assert property (@(posedge clk)
    api_rd_data ==
      (({32{api_addr[2:0]==3'd0}} & mem0_api_rd_data) |
       ({32{api_addr[2:0]==3'd1}} & mem1_api_rd_data) |
       ({32{api_addr[2:0]==3'd2}} & mem2_api_rd_data) |
       ({32{api_addr[2:0]==3'd3}} & mem3_api_rd_data) |
       ({32{api_addr[2:0]==3'd4}} & mem4_api_rd_data) |
       ({32{api_addr[2:0]==3'd5}} & mem5_api_rd_data) |
       ({32{api_addr[2:0]==3'd6}} & mem6_api_rd_data) |
       ({32{api_addr[2:0]==3'd7}} & mem7_api_rd_data))
  );

  // Registered API read path: 1-cycle latency from memory
  assert property (@(posedge clk) 1 |=> (mem0_api_rd_data == $past(mem0[api_addr[7:3]])));
  assert property (@(posedge clk) 1 |=> (mem1_api_rd_data == $past(mem1[api_addr[7:3]])));
  assert property (@(posedge clk) 1 |=> (mem2_api_rd_data == $past(mem2[api_addr[7:3]])));
  assert property (@(posedge clk) 1 |=> (mem3_api_rd_data == $past(mem3[api_addr[7:3]])));
  assert property (@(posedge clk) 1 |=> (mem4_api_rd_data == $past(mem4[api_addr[7:3]])));
  assert property (@(posedge clk) 1 |=> (mem5_api_rd_data == $past(mem5[api_addr[7:3]])));
  assert property (@(posedge clk) 1 |=> (mem6_api_rd_data == $past(mem6[api_addr[7:3]])));
  assert property (@(posedge clk) 1 |=> (mem7_api_rd_data == $past(mem7[api_addr[7:3]])));

  // Registered internal read path: 1-cycle latency from memory
  assert property (@(posedge clk) 1 |=> (mem0_int_rd_data == $past(mem0[internal_addr])));
  assert property (@(posedge clk) 1 |=> (mem1_int_rd_data == $past(mem1[internal_addr])));
  assert property (@(posedge clk) 1 |=> (mem2_int_rd_data == $past(mem2[internal_addr])));
  assert property (@(posedge clk) 1 |=> (mem3_int_rd_data == $past(mem3[internal_addr])));
  assert property (@(posedge clk) 1 |=> (mem4_int_rd_data == $past(mem4[internal_addr])));
  assert property (@(posedge clk) 1 |=> (mem5_int_rd_data == $past(mem5[internal_addr])));
  assert property (@(posedge clk) 1 |=> (mem6_int_rd_data == $past(mem6[internal_addr])));
  assert property (@(posedge clk) 1 |=> (mem7_int_rd_data == $past(mem7[internal_addr])));

  // Internal read data concatenation order
  assert property (@(posedge clk)
    internal_rd_data == {mem7_int_rd_data,mem6_int_rd_data,mem5_int_rd_data,mem4_int_rd_data,
                         mem3_int_rd_data,mem2_int_rd_data,mem1_int_rd_data,mem0_int_rd_data});

  // Write correctness: write takes effect next cycle at selected bank/address
  assert property (@(posedge clk) mem0_we |=> (mem0[$past(api_addr[7:3])] == $past(api_wr_data)));
  assert property (@(posedge clk) mem1_we |=> (mem1[$past(api_addr[7:3])] == $past(api_wr_data)));
  assert property (@(posedge clk) mem2_we |=> (mem2[$past(api_addr[7:3])] == $past(api_wr_data)));
  assert property (@(posedge clk) mem3_we |=> (mem3[$past(api_addr[7:3])] == $past(api_wr_data)));
  assert property (@(posedge clk) mem4_we |=> (mem4[$past(api_addr[7:3])] == $past(api_wr_data)));
  assert property (@(posedge clk) mem5_we |=> (mem5[$past(api_addr[7:3])] == $past(api_wr_data)));
  assert property (@(posedge clk) mem6_we |=> (mem6[$past(api_addr[7:3])] == $past(api_wr_data)));
  assert property (@(posedge clk) mem7_we |=> (mem7[$past(api_addr[7:3])] == $past(api_wr_data)));

  // Covers

  // Bank selection exercised
  cover property (@(posedge clk) api_addr[2:0]==3'd0);
  cover property (@(posedge clk) api_addr[2:0]==3'd1);
  cover property (@(posedge clk) api_addr[2:0]==3'd2);
  cover property (@(posedge clk) api_addr[2:0]==3'd3);
  cover property (@(posedge clk) api_addr[2:0]==3'd4);
  cover property (@(posedge clk) api_addr[2:0]==3'd5);
  cover property (@(posedge clk) api_addr[2:0]==3'd6);
  cover property (@(posedge clk) api_addr[2:0]==3'd7);

  // Writes to each bank exercised
  cover property (@(posedge clk) api_we && (api_addr[2:0]==3'd0));
  cover property (@(posedge clk) api_we && (api_addr[2:0]==3'd1));
  cover property (@(posedge clk) api_we && (api_addr[2:0]==3'd2));
  cover property (@(posedge clk) api_we && (api_addr[2:0]==3'd3));
  cover property (@(posedge clk) api_we && (api_addr[2:0]==3'd4));
  cover property (@(posedge clk) api_we && (api_addr[2:0]==3'd5));
  cover property (@(posedge clk) api_we && (api_addr[2:0]==3'd6));
  cover property (@(posedge clk) api_we && (api_addr[2:0]==3'd7));

  // Write -> API readback after two cycles with stable bank/address
  cover property (@(posedge clk)
    api_we
    ##1 (api_addr[2:0]==$past(api_addr[2:0]) && api_addr[7:3]==$past(api_addr[7:3]))
    ##1 (api_addr[2:0]==$past(api_addr[2:0],2) && api_addr[7:3]==$past(api_addr[7:3],2) &&
         api_rd_data == $past(api_wr_data,2))
  );

  // Internal pipeline: address change reflected next cycle
  cover property (@(posedge clk) $changed(internal_addr) ##1 $changed(internal_rd_data));

endmodule

// Bind into the DUT
bind blockmem_rw32_r128 blockmem_rw32_r128_sva u_blockmem_rw32_r128_sva (
  .clk               (clk),
  .api_we            (api_we),
  .api_addr          (api_addr),
  .api_wr_data       (api_wr_data),
  .api_rd_data       (api_rd_data),
  .internal_addr     (internal_addr),
  .internal_rd_data  (internal_rd_data),

  .mem0_api_rd_data  (mem0_api_rd_data),
  .mem1_api_rd_data  (mem1_api_rd_data),
  .mem2_api_rd_data  (mem2_api_rd_data),
  .mem3_api_rd_data  (mem3_api_rd_data),
  .mem4_api_rd_data  (mem4_api_rd_data),
  .mem5_api_rd_data  (mem5_api_rd_data),
  .mem6_api_rd_data  (mem6_api_rd_data),
  .mem7_api_rd_data  (mem7_api_rd_data),

  .mem0_int_rd_data  (mem0_int_rd_data),
  .mem1_int_rd_data  (mem1_int_rd_data),
  .mem2_int_rd_data  (mem2_int_rd_data),
  .mem3_int_rd_data  (mem3_int_rd_data),
  .mem4_int_rd_data  (mem4_int_rd_data),
  .mem5_int_rd_data  (mem5_int_rd_data),
  .mem6_int_rd_data  (mem6_int_rd_data),
  .mem7_int_rd_data  (mem7_int_rd_data),

  .mem0_we           (mem0_we),
  .mem1_we           (mem1_we),
  .mem2_we           (mem2_we),
  .mem3_we           (mem3_we),
  .mem4_we           (mem4_we),
  .mem5_we           (mem5_we),
  .mem6_we           (mem6_we),
  .mem7_we           (mem7_we),

  .mem0              (mem0),
  .mem1              (mem1),
  .mem2              (mem2),
  .mem3              (mem3),
  .mem4              (mem4),
  .mem5              (mem5),
  .mem6              (mem6),
  .mem7              (mem7)
);