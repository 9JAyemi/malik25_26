// SVA for ac97commands
`ifndef SYNTHESIS
module ac97commands_sva (
  input  logic        clock,
  input  logic        ready,
  input  logic [7:0]  command_address,
  input  logic [15:0] command_data,
  input  logic        command_valid,
  input  logic [4:0]  volume,
  input  logic [2:0]  source,
  input  logic [23:0] command,
  input  logic [3:0]  state,
  input  logic [4:0]  vol
);

  default clocking cb @(posedge clock); endclocking

  function automatic [23:0] exp_cmd (input logic [3:0] st,
                                     input logic [4:0] volume_i,
                                     input logic [2:0] source_i);
    logic [4:0] v;
    begin
      v = 5'd31 - volume_i;
      unique case (st)
        4'h0:     exp_cmd = 24'h80_0000;
        4'h1:     exp_cmd = 24'h80_0000;
        4'h3:     exp_cmd = {8'h04, 3'b000, v, 3'b000, v};
        4'h5:     exp_cmd = 24'h18_0808;
        4'h6:     exp_cmd = {8'h1A, 5'b00000, source_i, 5'b00000, source_i};
        4'h7:     exp_cmd = 24'h1C_0F0F;
        4'h9:     exp_cmd = 24'h0E_8048;
        4'hA:     exp_cmd = 24'h0A_0000;
        4'hB:     exp_cmd = 24'h20_8000;
        default:  exp_cmd = 24'h80_0000;
      endcase
    end
  endfunction

  // Command content matches state-driven spec (incl. vol/source mapping)
  a_cmd_map:      assert property (command == exp_cmd(state, volume, source));
  // Output split matches internal command bus
  a_split_match:  assert property ({command_address, command_data} == command);
  // Volume invert mapping
  a_vol_map:      assert property (vol == 5'd31 - volume);
  // State update: +1 when ready, hold when not (guard past on first cycle)
  a_state_step:   assert property ($past(1'b1) |-> state == $past(state) + ($past(ready) ? 4'd1 : 4'd0));
  // command_valid behavior per RTL: asserted in state 0 and sticky thereafter
  a_valid_in_s0:  assert property (state == 4'h0 |-> command_valid);
  a_valid_sticky: assert property ($past(command_valid) |-> command_valid);

  // Functional coverage
  // Hit all programmed states plus at least one defaulted state
  c_s0:  cover property (state == 4'h0);
  c_s1:  cover property (state == 4'h1);
  c_s3:  cover property (state == 4'h3);
  c_s5:  cover property (state == 4'h5);
  c_s6:  cover property (state == 4'h6);
  c_s7:  cover property (state == 4'h7);
  c_s9:  cover property (state == 4'h9);
  c_sA:  cover property (state == 4'hA);
  c_sB:  cover property (state == 4'hB);
  c_s2_default: cover property (state == 4'h2);

  // Corner values on programmable fields
  c_vol_min: cover property (state == 4'h3 && volume == 5'd0);
  c_vol_max: cover property (state == 4'h3 && volume == 5'd31);
  c_src_min: cover property (state == 4'h6 && source == 3'd0);
  c_src_max: cover property (state == 4'h6 && source == 3'd7);

  // Observe a ready-driven increment
  c_ready_inc: cover property ($past(ready) && (state == $past(state) + 4'd1));

endmodule

bind ac97commands ac97commands_sva sva_i (.*);
`endif