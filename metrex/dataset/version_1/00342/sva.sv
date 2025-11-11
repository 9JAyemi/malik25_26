// Bind these SVA modules to the DUT. Concise, high-value checks and covers.

////////////////////////////////////////////////////////////
// up_down_counter assertions
////////////////////////////////////////////////////////////
module up_down_counter_sva;
  // Access DUT signals directly via bind scope
  default clocking cb @(posedge clk); endclocking

  bit started;
  initial started = 1'b0;
  always @(posedge clk) started <= 1'b1;

  // Reset takes effect immediately on the clock edge
  ap_reset: assert property (reset |-> (count == 4'h0));

  // Load has priority over up_down
  ap_load:  assert property (!reset && load |-> (count == data_in));

  // Increment when up_down and no reset/load
  ap_inc:   assert property (disable iff (!started)
                             (!reset && !load && up_down)
                             |-> (count == (($past(count)+5'd1) % 5'd16)));

  // Decrement when !up_down and no reset/load
  ap_dec:   assert property (disable iff (!started)
                             (!reset && !load && !up_down)
                             |-> (count == (($past(count)+5'd15) % 5'd16)));

  // No X/Z on output when not in reset
  ap_no_x:  assert property (!reset |-> !$isunknown(count));

  // Covers
  cv_reset: cover property (reset);
  cv_load:  cover property (!reset && load);
  cv_inc:   cover property (!reset && !load && up_down);
  cv_dec:   cover property (!reset && !load && !up_down);

  // Wrap-around covers
  cv_wrap_up:  cover property (disable iff (!started)
                               (!reset && !load && up_down && $past(count)==4'hF && count==4'h0));
  cv_wrap_dn:  cover property (disable iff (!started)
                               (!reset && !load && !up_down && $past(count)==4'h0 && count==4'hF));
endmodule

bind up_down_counter up_down_counter_sva;


////////////////////////////////////////////////////////////
// magnitude_comparator assertions
// Combinational checking via immediate assertions
////////////////////////////////////////////////////////////
module magnitude_comparator_sva;
  always_comb begin
    // Legal select encodings
    if (select === 1'b0) begin
      assert (input_selected == 2'b00)
        else $error("input_selected must be 00 when select==0");
      assert (comparison_result ==
              ((a > b) ? 3'b001 :
               (a == b) ? 3'b010 :
                          3'b100))
        else $error("comparison_result mismatch for select==0");
    end
    else if (select === 1'b1) begin
      assert (input_selected == 2'b01)
        else $error("input_selected must be 01 when select==1");
      assert (comparison_result ==
              ((b > a) ? 3'b001 :
               (a == b) ? 3'b010 :
                          3'b100))
        else $error("comparison_result mismatch for select==1");
    end
    else begin
      // Defensive: undefined select drives default outputs
      assert (comparison_result == 3'b000)
        else $error("comparison_result must be 000 for undefined select");
      assert (input_selected == 2'b00)
        else $error("input_selected must be 00 for undefined select");
    end

    // When select is legal, result must be one of the three encodings
    if (select inside {1'b0,1'b1}) begin
      assert (comparison_result inside {3'b001,3'b010,3'b100})
        else $error("comparison_result must be 001/010/100 for legal select");
    end
  end
endmodule

bind magnitude_comparator magnitude_comparator_sva;


////////////////////////////////////////////////////////////
// top_module assertions (connectivity + functional covers)
////////////////////////////////////////////////////////////
module top_module_sva;
  default clocking cb @(posedge clk); endclocking

  // Connectivity: counter load value is {a,1'b0}
  ap_cnt_di_conn: assert property (counter.data_in == {a,1'b0});

  // Functional: on load, count must immediately reflect {a,1'b0}
  ap_cnt_load_to_a0: assert property (!reset && load |-> (count == {a,1'b0}));

  // Comparator select mapping to input_selected
  ap_sel_map0: assert property (select==1'b0 |-> input_selected==2'b00);
  ap_sel_map1: assert property (select==1'b1 |-> input_selected==2'b01);

  // Coverage for comparator outcomes under both select values
  cv_cmp_s0_gt: cover property (select==1'b0 && (a > b)  && comparison_result==3'b001);
  cv_cmp_s0_eq: cover property (select==1'b0 && (a == b) && comparison_result==3'b010);
  cv_cmp_s0_lt: cover property (select==1'b0 && (a < b)  && comparison_result==3'b100);

  cv_cmp_s1_gt: cover property (select==1'b1 && (b > a)  && comparison_result==3'b001);
  cv_cmp_s1_eq: cover property (select==1'b1 && (a == b) && comparison_result==3'b010);
  cv_cmp_s1_lt: cover property (select==1'b1 && (b < a)  && comparison_result==3'b100);
endmodule

bind top_module top_module_sva;