module CtorMod(input  logic       clk,
               input  logic       start,
               output logic [7:0] threads);
  class Pool;
    int numThreads;
    function new(int n);
      numThreads = (n > 1) ? n : 1;
    endfunction
    function int getThreads();
      return numThreads;
    endfunction
  endclass
  Pool p;
  always_ff @(posedge clk) begin
    if (start) begin
      p = new(4);
      threads <= p.getThreads();
    end
  end
endmodule
module DestructorMod(input  logic clk,
                     input  logic kill,
                     output logic killed);
  class Pool;
    bit shutdown;
    function new();
      shutdown = 0;
    endfunction
    function void shutdownPool();
      shutdown = 1;
    endfunction
    function bit isShutdown();
      return shutdown;
    endfunction
  endclass
  Pool p;
  always_ff @(posedge clk) begin
    if (kill) begin
      p = new();
      p.shutdownPool();
      if (p.isShutdown()) killed <= 1;
    end
  end
endmodule
module EnqueueMod(input  logic       clk,
                  input  logic       enqueue,
                  input  logic [7:0] data_in,
                  output logic [7:0] data_out);
  class Enq;
    bit [7:0] q[$];
    function void add(bit [7:0] val);
      q.push_back(val);
    endfunction
    function bit [7:0] remove();
      if (q.size() == 0) return 0;
      return q.pop_front();
    endfunction
    function int size();
      return q.size();
    endfunction
  endclass
  Enq eq;
  always_ff @(posedge clk) begin
    if (enqueue) begin
      if (eq == null) eq = new();
      eq.add(data_in);
    end
    if (eq != null && eq.size() > 0) begin
      data_out <= eq.remove();
    end
  end
endmodule
module WaitMod(input  logic clk,
               input  logic go,
               output logic done);
  class WaitC;
    int pendingJobs;
    bit shutdown;
    function new();
      pendingJobs = 0;
      shutdown    = 0;
    endfunction
    function void inc();
      pendingJobs++;
    endfunction
    function void dec();
      pendingJobs--;
    endfunction
    function void setShutdown();
      shutdown = 1;
    endfunction
    function bit checkDone();
      return (pendingJobs == 0) || shutdown;
    endfunction
  endclass
  WaitC w;
  always_ff @(posedge clk) begin
    if (go) begin
      if (w == null) w = new();
      w.inc();
      w.setShutdown();
      if (w.checkDone()) done <= 1;
    end
  end
endmodule
module StartWorkerMod(input  logic clk,
                      input  logic enable,
                      output logic started);
  class Worker;
    bit started_flag;
    function new();
      started_flag = 0;
    endfunction
    function void start();
      started_flag = 1;
    endfunction
    function bit isStarted();
      return started_flag;
    endfunction
  endclass
  Worker w;
  always_ff @(posedge clk) begin
    if (enable) begin
      w = new();
      w.start();
      started <= w.isStarted();
    end
  end
endmodule
module WorkerLoopMod(input  logic        clk,
                     input  logic        enq,
                     input  logic [3:0]  depth,
                     output logic [3:0]  processed);
  class WorkerLoop;
    bit shutdown;
    int queue[$];
    function new();
      shutdown = 0;
    endfunction
    function void enqueue(int job);
      queue.push_back(job);
    endfunction
    function void shutdownPool();
      shutdown = 1;
    endfunction
    task runLoop(ref logic [3:0] proc);
      proc = 0;
      while (!shutdown) begin
        if (queue.size() != 0) begin
          queue.pop_front();
          proc++;
        end else disable runLoop;
      end
    endtask
  endclass
  WorkerLoop wl;
  always_ff @(posedge clk) begin
    if (enq) begin
      if (wl == null) wl = new();
      wl.enqueue(depth);
      if (depth == 0) wl.shutdownPool();
      wl.runLoop(processed);
    end
  end
endmodule
module SelfTestMod(input  logic clk,
                   input  logic go,
                   output logic success);
  class TestClass;
    int commonValue;
    function new();
      commonValue = 0;
    endfunction
    function void firstJob(int sleep);
      commonValue = 10;
    endfunction
    function void secondJob(int sleep);
      commonValue = 1000;
    endfunction
    function void thirdJob(int sleep);
      commonValue = 100;
    endfunction
    function int getValue();
      return commonValue;
    endfunction
  endclass
  TestClass t;
  always_ff @(posedge clk) begin
    if (go) begin
      t = new();
      t.firstJob(100);
      t.secondJob(200);
      t.thirdJob(300);
      success <= (t.getValue() == 100) ||
                 (t.getValue() == 1000) ||
                 (t.getValue() == 10);
    end
  end
endmodule
module ThreadScopeMod(input  logic clk,
                      input  logic start,
                      output logic ok);
  class ThreadScope;
    int scoped;
    function new();
      scoped = 1;
    endfunction
    function void enqueue();
      scoped = 2;
    endfunction
    function void do_wait();
      scoped = 3;
    endfunction
    function bit done();
      return scoped == 3;
    endfunction
  endclass
  ThreadScope ts;
  always_ff @(posedge clk) begin
    if (start) begin
      ts = new();
      ts.enqueue();
      ts.do_wait();
      ok <= ts.done();
    end
  end
endmodule
