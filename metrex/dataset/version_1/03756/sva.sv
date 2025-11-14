// SVA for encode_ctl
// Bind these assertions into the DUT: bind encode_ctl encode_ctl_sva u_encode_ctl_sva();

module encode_ctl_sva;

  // Use DUT scope names via bind (no ports)
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Fundamental flop-follow properties
  assert property (state == $past(state_next)) else $error("state != state_next");
  assert property (cnt_output      == $past(cnt_output_next)) else $error("cnt_output mismatch");
  assert property (cnt_len         == $past(cnt_len_next))    else $error("cnt_len mismatch");
  assert property (cnt_output_enable == $past(cnt_output_enable_next))
         else $error("cnt_output_enable mismatch");
  assert property (cnt_finish == (state == S_STOP)) else $error("cnt_finish mismatch");

  // iidx_window behavior
  assert property (iidx[11] |=> iidx_window) else $error("iidx_window not set on iidx[11]");
  assert property (iidx_window |=> iidx_window) else $error("iidx_window not sticky");

  // min_off/max_off/off/off_valid
  assert property ((data_valid && iidx_window) |=> min_off == $past(min_off)+1)
         else $error("min_off increment error");
  assert property (!(data_valid && iidx_window) |=> min_off == $past(min_off))
         else $error("min_off hold error");

  assert property (data_valid |=> max_off == iidx) else $error("max_off update error");
  assert property (!data_valid |=> max_off == $past(max_off)) else $error("max_off hold error");

  assert property (off == (max_off - hash_ref)) else $error("off difference mismatch");
  assert property (off_valid == ((hash_ref > min_off) && (hash_ref < max_off)))
         else $error("off_valid definition mismatch");

  // Addressing and rallow
  assert property (rallow == (cnt_load || cnt_count)) else $error("rallow definition mismatch");
  assert property (hraddr == (rallow ? raddr_plus_one : raddr_reg))
         else $error("hraddr mux mismatch");
  assert property (hash_ref_plus_one == hash_ref + 1) else $error("hash_ref_plus_one mismatch");

  // raddr pipelines
  assert property (cnt_load |=> (raddr_plus_one == (hash_ref_plus_one + 1) &&
                                 raddr_reg      ==  hash_ref_plus_one))
         else $error("raddr load update mismatch");

  assert property (cnt_count && !cnt_load |=> (raddr_plus_one == $past(raddr_plus_one) + 1 &&
                                               raddr_reg      == $past(raddr_plus_one)))
         else $error("raddr count update mismatch");

  assert property (!(cnt_load || cnt_count) |=> (raddr_plus_one == $past(raddr_plus_one) &&
                                                 raddr_reg      == $past(raddr_reg)))
         else $error("raddr hold mismatch");

  // Counter machine (cnt, cnt_big7)
  // Load
  assert property (cnt_load |=> (cnt == 4'd2 && cnt_big7 == 1'b0))
         else $error("cnt/cnt_big7 load mismatch");

  // Count paths
  assert property (cnt_count && (cnt_big7==0) && (cnt==4'd7) |=> (cnt==4'd0 && cnt_big7==1))
         else $error("cnt==7 transition mismatch");
  assert property (cnt_count && (cnt==4'd15) |=> (cnt==4'd1 && cnt_big7==$past(cnt_big7)))
         else $error("cnt==15 wrap mismatch");
  assert property (cnt_count && (cnt_big7==0) && !(cnt inside {4'd7,4'd15})
                   |=> (cnt == $past(cnt)+1 && cnt_big7==0))
         else $error("cnt increment (pre-big7) mismatch");
  assert property (cnt_count && (cnt_big7==1) && (cnt!=4'd15)
                   |=> (cnt == $past(cnt)+1 && cnt_big7==1))
         else $error("cnt increment (post-big7) mismatch");
  assert property (!(cnt_load || cnt_count) |=> (cnt==$past(cnt) && cnt_big7==$past(cnt_big7)))
         else $error("cnt/cnt_big7 hold mismatch");
  assert property (cnt_big7 && !cnt_load |=> cnt_big7) else $error("cnt_big7 should be sticky until load");

  // Output enable next in key situations
  assert property (state==S_SEARCH && data_valid |-> cnt_output_enable_next)
         else $error("SEARCH + data_valid should enable output");
  assert property (state==S_SEARCH && data_empty |-> cnt_output_enable_next)
         else $error("SEARCH + data_empty should enable output");

  assert property (state==S_TR && data_valid && !hash_data_d1 |-> cnt_output_enable_next)
         else $error("TR fall-through should enable output");
  assert property (state==S_TR && data_empty |-> cnt_output_enable_next)
         else $error("TR + data_empty should enable output");

  assert property (state==S_MATCH && data_valid && (data_d1 != hdata) |-> cnt_output_enable_next)
         else $error("MATCH mismatch should enable output");
  assert property (state==S_MATCH && data_empty |-> cnt_output_enable_next)
         else $error("MATCH + data_empty should enable output");

  assert property (state inside {S_END,S_DONE} |-> cnt_output_enable_next)
         else $error("END/DONE must enable output");

  // State decode key actions
  assert property (state==S_SEARCH && data_valid && (data_d2==hash_data) && off_valid
                   |-> (cnt_load && cnt_output_enable_next && state_next==S_TR))
         else $error("SEARCH match should load and go to TR");

  assert property (state==S_TR && data_valid && hash_data_d1
                   |-> (cnt_count && state_next==S_MATCH))
         else $error("TR accept should count and go to MATCH");

  assert property (state==S_TR && data_valid && !hash_data_d1
                   |-> (state_next==S_SEARCH))
         else $error("TR reject should return to SEARCH");

  assert property (state==S_MATCH && data_valid && (data_d1==hdata) |-> cnt_count)
         else $error("MATCH equality should count");

  assert property (state==S_MATCH && data_valid && (data_d1==hdata) &&
                   ((cnt==4'h7 && !cnt_big7) || (cnt==4'hf))
                   |-> cnt_output_enable_next)
         else $error("MATCH chunk boundary should enable output");

  // cnt_output_next/cnt_len_next selections in terminal/search states
  assert property (cnt_output_enable_next && state==S_END
                   |-> (cnt_len_next==4'h9 &&
                        cnt_output_next[8:0]==9'b110000000 &&
                        cnt_output_next[12:9]==4'b0000))
         else $error("END output format mismatch");

  assert property (cnt_output_enable_next && state==S_DONE
                   |-> (cnt_len_next==4'hf &&
                        cnt_output_next[8:0]==9'b000000000 &&
                        cnt_output_next[12:9]==4'b0000))
         else $error("DONE output format mismatch");

  assert property (cnt_output_enable_next && state==S_SEARCH
                   |-> (cnt_len_next==encode_len_s && cnt_output_next==encode_data_s))
         else $error("SEARCH output selection mismatch");

  // Dummy counter behavior
  assert property ((state==S_DONE) |=> dummy_cnt == $past(dummy_cnt)+1)
         else $error("dummy_cnt increment mismatch");
  assert property ((state!=S_DONE) |=> dummy_cnt == $past(dummy_cnt))
         else $error("dummy_cnt hold mismatch");

  // Cover: reach all states
  cover property (state==S_IDLE);
  cover property (state==S_DELAY);
  cover property (state==S_SEARCH);
  cover property (state==S_TR);
  cover property (state==S_MATCH);
  cover property (state==S_END);
  cover property (state==S_DONE);
  cover property (state==S_STOP);

  // Cover: successful match path SEARCH -> TR -> MATCH
  sequence s_match_path;
    state==S_SEARCH && data_valid && (data_d2==hash_data) && off_valid ##1
    state==S_TR     && data_valid && hash_data_d1        ##1
    state==S_MATCH;
  endsequence
  cover property (s_match_path);

  // Cover: cnt_big7 set at cnt==7 and boundary pulse
  cover property (state==S_MATCH && data_valid && (data_d1==hdata) &&
                  cnt_big7==0 && cnt==4'd7 ##1 (cnt_big7==1 && cnt==4'd0));

  // Cover: reach STOP (completion)
  cover property (state==S_STOP);

endmodule