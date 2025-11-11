// SVA for bitwise_rotation
// Bind this module to the DUT: 
// bind bitwise_rotation bitwise_rotation_sva sva_inst (.*);

module bitwise_rotation_sva (
  input  logic        clk,
  input  logic [25:0] Data_i,
  input  logic        select_i,
  input  logic        bit_shift_i,
  input  logic [25:0] Data_o,
  input  logic [25:0] temp
);
  // past-valid guard
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  // helpers
  function automatic [25:0] rotl1 (input [25:0] x);
    rotl1 = {x[24:0], x[25]};
  endfunction
  function automatic [25:0] rotr1 (input [25:0] x);
    rotr1 = {x[0], x[25:1]};
  endfunction

  // Stage-1 (temp) must be a 1-bit rotate per select_i
  assert property (@(posedge clk) disable iff (!past_valid)
    temp == (select_i ? rotr1(Data_i) : rotl1(Data_i))
  );

  // Output behavior: pass-through when bit_shift_i==1
  assert property (@(posedge clk) disable iff (!past_valid)
    $past(bit_shift_i) |-> Data_o == $past(Data_i)
  );

  // Output behavior: 1-bit rotate when bit_shift_i==0
  assert property (@(posedge clk) disable iff (!past_valid)
    ($past(bit_shift_i)==0 && $past(select_i)==0) |-> Data_o == rotl1($past(Data_i))
  );
  assert property (@(posedge clk) disable iff (!past_valid)
    ($past(bit_shift_i)==0 && $past(select_i)==1) |-> Data_o == rotr1($past(Data_i))
  );

  // Sanity: no X/Z on output
  assert property (@(posedge clk) !$isunknown(Data_o));

  // Coverage: exercise both rotations and pass-through
  cover property (@(posedge clk) disable iff (!past_valid)
    $past(bit_shift_i)==0 && $past(select_i)==0
  );
  cover property (@(posedge clk) disable iff (!past_valid)
    $past(bit_shift_i)==0 && $past(select_i)==1
  );
  cover property (@(posedge clk) disable iff (!past_valid)
    $past(bit_shift_i)==1
  );

  // Coverage: wrap-around edges observed
  cover property (@(posedge clk) disable iff (!past_valid)
    $past(bit_shift_i)==0 && $past(select_i)==0 && $past(Data_i[25]) && Data_o[0]
  );
  cover property (@(posedge clk) disable iff (!past_valid)
    $past(bit_shift_i)==0 && $past(select_i)==1 && $past(Data_i[0])  && Data_o[25]
  );
endmodule

// Example bind (connect internal temp)
// bind bitwise_rotation bitwise_rotation_sva sva (.*);