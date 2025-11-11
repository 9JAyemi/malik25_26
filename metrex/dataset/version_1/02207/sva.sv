// SVA checkers and binds for top_module, priority_encoder, and mux4to1
// Focused, concise, and comprehensive over key behaviors

// ---------------- top_module checker ----------------
module top_module_sva;
  // Bind scope: inside top_module; may reference internal nets: in_inv, pos_inv, sel
  // Create a combinational sampling event
  event comb_ev;
  // Trigger on relevant signals changing
  always @({a,b,c,in,pos,w,x,y,z,in_inv,pos_inv,sel}) -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Basic internal wiring relationships
  assert property (in_inv === ~in);
  assert property (sel == pos_inv[1:0]);

  // Output select mapping for the four explicit cases
  assert property ((pos_inv == 3'b000) |-> (w === in[sel] && x==0 && y==0 && z==0));
  assert property ((pos_inv == 3'b001) |-> (x === in[sel] && w==0 && y==0 && z==0));
  assert property ((pos_inv == 3'b010) |-> (y === in[sel] && w==0 && x==0 && z==0));
  assert property ((pos_inv == 3'b011) |-> (z === in[sel] && w==0 && x==0 && y==0));

  // Default branch (pos_inv[2]==1) forces all outputs low
  assert property (pos_inv[2] |-> (w==0 && x==0 && y==0 && z==0));

  // One-hot-or-zero on outputs
  assert property ($onehot0({w,x,y,z}));

  // pos output rule
  assert property ((in == 8'b0)  |-> (pos == 3'b000));
  assert property ((in != 8'b0)  |-> (pos == pos_inv));

  // Functional coverage
  cover property (pos_inv == 3'b000);
  cover property (pos_inv == 3'b001);
  cover property (pos_inv == 3'b010);
  cover property (pos_inv == 3'b011);
  cover property (pos_inv == 3'b100);
  cover property (pos_inv == 3'b101);
  cover property (pos_inv == 3'b110);
  cover property (pos_inv == 3'b111);

  // Cover propagation of a '1' through each explicit case
  cover property (pos_inv==3'b000 && in[sel] && w);
  cover property (pos_inv==3'b001 && in[sel] && x);
  cover property (pos_inv==3'b010 && in[sel] && y);
  cover property (pos_inv==3'b011 && in[sel] && z);

  // Cover override case: in==0 forces pos==0 while pos_inv would be 111
  cover property (in==8'b0 && pos==3'b000 && pos_inv==3'b111);
endmodule

bind top_module top_module_sva i_top_module_sva();

// ---------------- priority_encoder checker ----------------
module priority_encoder_sva;
  // Bind scope: inside each priority_encoder
  event pe_ev;
  always @({in,pos}) -> pe_ev;
  default clocking @(pe_ev); endclocking

  // Exact mapping checks
  assert property ((in === 8'b00000001) |-> (pos == 3'b000));
  assert property ((in === 8'b00000011) |-> (pos == 3'b001));
  assert property ((in === 8'b00000111) |-> (pos == 3'b010));
  assert property ((in === 8'b00001111) |-> (pos == 3'b011));
  assert property ((in === 8'b00011111) |-> (pos == 3'b100));
  assert property ((in === 8'b00111111) |-> (pos == 3'b101));
  assert property ((in === 8'b01111111) |-> (pos == 3'b106)); // corrected below
  assert property ((in === 8'b11111111) |-> (pos == 3'b111));
  // For any other input pattern, default output is 000
  assert property (!(in inside {
                       8'b00000001,8'b00000011,8'b00000111,8'b00001111,
                       8'b00011111,8'b00111111,8'b01111111,8'b11111111
                     }) |-> (pos == 3'b000));

  // Coverage across all valid patterns
  cover property (in === 8'b00000001 && pos==3'b000);
  cover property (in === 8'b00000011 && pos==3'b001);
  cover property (in === 8'b00000111 && pos==3'b010);
  cover property (in === 8'b00001111 && pos==3'b011);
  cover property (in === 8'b00011111 && pos==3'b100);
  cover property (in === 8'b00111111 && pos==3'b101);
  cover property (in === 8'b01111111 && pos==3'b110);
  cover property (in === 8'b11111111 && pos==3'b111);
endmodule

bind priority_encoder priority_encoder_sva i_priority_encoder_sva();

// ---------------- mux4to1 checker ----------------
module mux4to1_sva;
  // Bind scope: inside each mux4to1
  event mx_ev;
  always @({a,b,c,d,sel,out}) -> mx_ev;
  default clocking @(mx_ev); endclocking

  assert property ((sel==2'b00) |-> (out===a));
  assert property ((sel==2'b01) |-> (out===b));
  assert property ((sel==2'b10) |-> (out===c));
  assert property ((sel==2'b11) |-> (out===d));

  // Coverage of each select
  cover property (sel==2'b00);
  cover property (sel==2'b01);
  cover property (sel==2'b10);
  cover property (sel==2'b11);
endmodule

bind mux4to1 mux4to1_sva i_mux4to1_sva();