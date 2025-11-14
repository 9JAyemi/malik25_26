// SVA checker for cordic_demod
// Bind this file to the DUT
bind cordic_demod cordic_demod_sva u_cordic_demod_sva();

module cordic_demod_sva;
  // Implicitly inside cordic_demod scope via bind
  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn);

  // Ready/valid encodings
  assert property (s_axis_ready == (state == STATE_IDLE));
  assert property (m_axis_valid == (state == STATE_DONE));
  assert property (!resetn |-> state == STATE_IDLE);
  assert property (!resetn |-> s_axis_ready && !m_axis_valid);

  // Legal states and transitions
  assert property (state inside {STATE_IDLE,STATE_SHIFT_LOAD,STATE_SHIFT,STATE_ADD,STATE_DONE});
  assert property (state==STATE_IDLE && !s_axis_valid |=> state==STATE_IDLE);
  assert property (state==STATE_IDLE && s_axis_valid  |=> state==STATE_SHIFT_LOAD);
  assert property (state==STATE_SHIFT_LOAD && step_counter==0 |=> state==STATE_ADD);
  assert property (state==STATE_SHIFT_LOAD && step_counter!=0 |=> state==STATE_SHIFT);
  assert property (state==STATE_SHIFT && shift_counter==1 |=> state==STATE_ADD);
  assert property (state==STATE_SHIFT && shift_counter!=1 |=> state==STATE_SHIFT);
  assert property (state==STATE_ADD && step_counter==30 |=> state==STATE_DONE);
  assert property (state==STATE_ADD && step_counter!=30 |=> state==STATE_SHIFT_LOAD);
  assert property (state==STATE_DONE && !m_axis_ready |=> state==STATE_DONE);
  assert property (state==STATE_DONE &&  m_axis_ready |=> state==STATE_IDLE);

  // AXI-Stream input stability when not accepted
  assert property (s_axis_valid && !s_axis_ready |-> $stable(s_axis_data));

  // Progress: handshake leads to m_axis_valid within bounded cycles
  sequence hs; s_axis_valid && s_axis_ready; endsequence
  assert property (hs |-> ##[1:520] m_axis_valid);

  // Output data mapping and stability under backpressure
  assert property (m_axis_data == {q[32:1], i[32:1]});
  assert property (m_axis_valid && !m_axis_ready |=> m_axis_valid && $stable(m_axis_data) && $stable(i) && $stable(q) && $stable(step_counter));

  // Capture on input handshake
  assert property (state==STATE_IDLE && s_axis_valid && s_axis_ready |=> step_counter==0);
  assert property (state==STATE_IDLE && s_axis_valid && s_axis_ready |=> phase == {1'b0,$past(s_axis_data[61:32])});

  // Quadrant decode on handshake (sample next cycle)
  assert property (state==STATE_IDLE && s_axis_valid && s_axis_ready && $past(s_axis_data[63:62])==2'b00 |=> q=='h0 && i=={$past(s_axis_data[31]),$past(s_axis_data[31:0])});
  assert property (state==STATE_IDLE && s_axis_valid && s_axis_ready && $past(s_axis_data[63:62])==2'b01 |=> i=='h0 && q==~{$past(s_axis_data[31]),$past(s_axis_data[31:0])});
  assert property (state==STATE_IDLE && s_axis_valid && s_axis_ready && $past(s_axis_data[63:62])==2'b10 |=> q=='h0 && i==~{$past(s_axis_data[31]),$past(s_axis_data[31:0])});
  assert property (state==STATE_IDLE && s_axis_valid && s_axis_ready && $past(s_axis_data[63:62])==2'b11 |=> i=='h0 && q=={$past(s_axis_data[31]),$past(s_axis_data[31:0])});

  // Shift-load and shift behavior
  assert property (state==STATE_SHIFT_LOAD |=> shift_counter == $past(step_counter));
  assert property (state==STATE_SHIFT_LOAD |=> i_shift == $past(i) && q_shift == $past(q));
  assert property (state==STATE_SHIFT |=> shift_counter == $past(shift_counter)-1
                                    && i_shift == {$past(i_shift)[32],$past(i_shift)[32:1]}
                                    && q_shift == {$past(q_shift)[32],$past(q_shift)[32:1]});

  // ADD behavior and step count
  assert property (state==STATE_ADD |=> step_counter == $past(step_counter)+1);
  assert property (state==STATE_ADD && !$past(phase[30]) |=> i==$past(i)+$past(q_shift)
                                                      && q==$past(q)-$past(i_shift)
                                                      && phase==$past(phase)-angle[$past(step_counter)]);
  assert property (state==STATE_ADD &&  $past(phase[30]) |=> i==$past(i)-$past(q_shift)
                                                      && q==$past(q)+$past(i_shift)
                                                      && phase==$past(phase)+angle[$past(step_counter)]);
  // step_counter stability when not ADD and not re-init
  assert property ((state!=STATE_ADD) && !(state==STATE_IDLE && s_axis_valid) |=> $stable(step_counter));

  // Outputs/regs stability in states that don't update them
  assert property ((state inside {STATE_SHIFT_LOAD,STATE_SHIFT,STATE_DONE}) |=> $stable(i) && $stable(q));

  // Angle table immutable
  genvar k;
  generate
    for (k=0; k<=30; k++) begin : ANG_STABLE
      assert property ($stable(angle[k]));
    end
  endgenerate

  // Useful covers
  cover property (hs);
  cover property (hs ##[1:$] m_axis_valid);
  cover property (m_axis_valid && !m_axis_ready ##1 m_axis_valid && m_axis_ready);
  cover property (state==STATE_ADD &&  $past(phase[30]));
  cover property (state==STATE_ADD && !$past(phase[30]));
  cover property (state==STATE_IDLE && s_axis_valid && s_axis_ready && s_axis_data[63:62]==2'b00);
  cover property (state==STATE_IDLE && s_axis_valid && s_axis_ready && s_axis_data[63:62]==2'b01);
  cover property (state==STATE_IDLE && s_axis_valid && s_axis_ready && s_axis_data[63:62]==2'b10);
  cover property (state==STATE_IDLE && s_axis_valid && s_axis_ready && s_axis_data[63:62]==2'b11);
endmodule