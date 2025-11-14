// Bindable SVA for top_module
bind top_module top_module_sva();

module top_module_sva;

  // Access bound instance signals directly
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Helpers
  function automatic [99:0] rotl100(input [99:0] v, input int k);
    int kk; begin
      kk = (k % 100);
      rotl100 = (v << kk) | (v >> (100-kk));
    end
  endfunction

  function automatic [31:0] byteswap32(input [31:0] x);
    return {x[7:0], x[15:8], x[23:16], x[31:24]};
  endfunction

  function automatic [9:0] sum4bytes(input [31:0] x);
    return x[7:0] + x[15:8] + x[23:16] + x[31:24];
  endfunction

  // Sanity: inputs known when used
  a_inputs_known_on_load: assert property (past_valid && load |-> !$isunknown({data,in}));
  a_rot_amt_known_on_rotate: assert property (past_valid && !load && (ena[0] || ena[1]) |-> !$isunknown(rot_amt));

  // ROTATOR always block behavior
  a_load_updates_rot_regs: assert property (
    past_valid && load |=> (rot_data == data) && (rot_in == in) && (rot_amt == in[4:0])
  );

  a_ena0_rotates_only_data: assert property (
    past_valid && !load && ena[0] && !ena[1] |=> 
      (rot_data == rotl100($past(rot_data), $past(rot_amt))) &&
      $stable(rot_out)
  );

  a_ena1_rotates_and_updates_rot_out: assert property (
    past_valid && !load && ena[1] && !ena[0] |=> 
      (rot_data == rotl100($past(rot_data), $past(rot_amt))) &&
      (rot_out  == {$past(rot_data[31:24]), $past(rot_data[23:16]), $past(rot_data[15:8]), $past(rot_data[7:0])})
  );

  a_rot_regs_hold_when_idle: assert property (
    past_valid && !load && !ena[0] && !ena[1] |=> 
      $stable({rot_data,rot_in,rot_amt,rot_out})
  );

  // BYTE ORDERING always block behavior
  a_ena1_updates_byte_pipe: assert property (
    past_valid && ena[1] |=> 
      (byte_in  == $past(rot_out)) &&
      (byte_out == byteswap32($past(byte_in)))
  );

  a_byte_regs_hold_when_no_ena1: assert property (
    past_valid && !ena[1] |=> $stable({byte_in,byte_out})
  );

  // SUM always block behavior
  a_ena1_updates_sum: assert property (
    past_valid && ena[1] |=> sum == sum4bytes($past(byte_out))[7:0]
  );

  a_sum_holds_when_no_ena1: assert property (
    past_valid && !ena[1] |=> $stable(sum)
  );

  // Priority/corner behavior when both ena bits high (else-if in rotator, independent in others)
  a_both_ena_priority_and_pipes: assert property (
    past_valid && !load && ena[0] && ena[1] |=> 
      (rot_data == rotl100($past(rot_data), $past(rot_amt))) &&
      $stable(rot_out) &&
      (byte_in  == $past(rot_out)) &&
      (byte_out == byteswap32($past(byte_in))) &&
      (sum      == sum4bytes($past(byte_out))[7:0])
  );

  // Coverage
  c_load:                 cover property (past_valid && load);
  c_rotate0:              cover property (past_valid && !load && ena[0] && (rot_amt==0));
  c_rotate1:              cover property (past_valid && !load && ena[0] && (rot_amt==1));
  c_rotate31:             cover property (past_valid && !load && ena[0] && (rot_amt==31));
  c_ena1_once:            cover property (past_valid && ena[1]);
  c_ena1_twice_pipeline:  cover property (past_valid && ena[1] ##1 ena[1]);
  c_both_ena:             cover property (past_valid && !load && ena[0] && ena[1]);
  c_idle_hold:            cover property (past_valid && !load && !ena[0] && !ena[1]);

endmodule