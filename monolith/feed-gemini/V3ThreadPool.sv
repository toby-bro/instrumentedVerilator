`define UASSERT(CONDITION, MESSAGE) \
    if (!(CONDITION)) begin \
        $error("ASSERTION FAILED: %0s", MESSAGE); \
    end
class SV_V3Mutex;
    semaphore lock_sem;
    function new();
        lock_sem = new(1);
    endfunction
    task lock();
        lock_sem.get(1);
    endtask
    task unlock();
        lock_sem.put(1);
    endtask
endclass
class SV_V3LockGuard;
    SV_V3Mutex m_mutex;
    function new(SV_V3Mutex mutex_ref);
        m_mutex = mutex_ref;
    endfunction
    task acquire();
        m_mutex.lock();
    endtask
    task do_release(); 
        m_mutex.unlock();
    endtask
endclass
class SV_V3Job;
    bit executed_flag;
    function new();
        executed_flag = 0;
    endfunction
    virtual task execute();
        executed_flag = 1;
    endtask
    function bit is_executed();
        return executed_flag;
    endfunction
endclass
typedef class SV_V3ThreadPool_Sim;
class SV_V3Global;
    SV_V3ThreadPool_Sim m_threadPoolp;
    protected function new();
    endfunction
    static function SV_V3Global get_instance();
        static SV_V3Global instance_local; 
        if (instance_local == null) begin
            instance_local = new();
        end
        return instance_local;
    endfunction
    function void set_threadPoolp(SV_V3ThreadPool_Sim pool);
        m_threadPoolp = pool;
    endfunction
    function SV_V3ThreadPool_Sim threadPoolp();
        return m_threadPoolp;
    endfunction
endclass
class SV_V3ThreadPool_Sim;
    int m_numThreads;
    SV_V3Mutex m_mutex;
    bit m_shutdown;
    int m_pendingJobs;
    SV_V3Job m_queue[$];
    event m_cv_notify;
    function new(int numThreads);
        m_mutex = new();
        this.m_numThreads = numThreads > 0 ? numThreads : 1;
        m_pendingJobs = 0;
        m_shutdown = 0;
        if (this.m_numThreads == 1) begin
        end else begin
            for (int i = 0; i < this.m_numThreads; ++i) begin
                fork
                    workerJobLoop();
                join_none
            end
        end
    endfunction
    task shutdown_pool();
        SV_V3LockGuard lock;
        lock = new(m_mutex);
        lock.acquire();
        m_shutdown = 1;
        lock.do_release(); 
        -> m_cv_notify;
        wait_for_all_jobs();
    endtask
    task wait_for_all_jobs();
        while (m_pendingJobs > 0 && !m_shutdown) begin
        end
        if (m_shutdown) begin
        end
    endtask
    task enqueue(SV_V3Job f);
        if (m_numThreads <= 1) begin
            f.execute();
        end else begin
            SV_V3LockGuard lock;
            lock = new(m_mutex);
            lock.acquire();
            m_queue.push_back(f);
            lock.do_release(); 
            m_pendingJobs++;
            -> m_cv_notify;
        end
    endtask
    task workerJobLoop();
        SV_V3Job job_to_execute;
        SV_V3LockGuard lock_guard_handle;
        forever begin
            lock_guard_handle = new(m_mutex);
            lock_guard_handle.acquire();
            while (! (m_queue.size() > 0 || m_shutdown) ) begin
                lock_guard_handle.do_release(); 
                wait(m_cv_notify.triggered);
                lock_guard_handle.acquire();
            end
            if (m_shutdown) begin
                lock_guard_handle.do_release(); 
                return;
            end
            `UASSERT(m_queue.size() > 0, "Job should be available");
            if (m_queue.size() == 0) begin
                lock_guard_handle.do_release(); 
                continue;
            end
            job_to_execute = m_queue.pop_front();
            lock_guard_handle.do_release(); 
            job_to_execute.execute();
            m_pendingJobs--;
        end
    endtask
endclass
class SV_V3ThreadScope;
    SV_V3ThreadPool_Sim m_pool;
    function new();
        `UASSERT(SV_V3Global::get_instance().threadPoolp() != null, "ThreadPool must be initialized before ThreadScope.");
        m_pool = SV_V3Global::get_instance().threadPoolp();
    endfunction
    task initial_wait_scope_jobs();
        m_pool.wait_for_all_jobs();
    endtask
    task enqueue(SV_V3Job f);
        m_pool.enqueue(f);
    endtask
    task perform_wait_scope_jobs();
        m_pool.wait_for_all_jobs();
    endtask
endclass
class SV_IntWrapper;
    int value;
    function new(int initial_value);
        value = initial_value;
    endfunction
    function int get();
        return value;
    endfunction
    function void set(int new_value);
        value = new_value;
    endfunction
endclass
class ConcreteJob1 extends SV_V3Job;
    bit internal_flag;
    function new(bit initial_flag);
        super.new();
        internal_flag = initial_flag;
    endfunction
    task execute();
        super.execute();
        internal_flag = !internal_flag;
    endtask
    function bit get_flag(); return internal_flag; endfunction
endclass
class ConcreteJob2 extends SV_V3Job;
    SV_IntWrapper value_handle;
    function new(SV_IntWrapper handle_ref);
        super.new();
        value_handle = handle_ref;
    endfunction
    task execute();
        super.execute();
        value_handle.set(value_handle.get() + 10);
    endtask
endclass
class IncrementJob extends SV_V3Job;
    SV_IntWrapper counter_handle;
    function new(SV_IntWrapper handle_ref);
        super.new();
        counter_handle = handle_ref;
    endfunction
    task execute();
        super.execute();
        counter_handle.set(counter_handle.get() + 1);
    endtask
endclass
class MultiplyJob extends SV_V3Job;
    SV_IntWrapper value_handle;
    function new(SV_IntWrapper handle_ref);
        super.new();
        value_handle = handle_ref;
    endfunction
    task execute();
        super.execute();
        value_handle.set(value_handle.get() * 3);
    endtask
endclass
class AddJob extends SV_V3Job;
    SV_IntWrapper value_handle;
    function new(SV_IntWrapper handle_ref);
        super.new();
        value_handle = handle_ref;
    endfunction
    task execute();
        super.execute();
        value_handle.set(value_handle.get() + 5);
    endtask
endclass
class FirstJobExecutor extends SV_V3Job;
    int m_sleep_iter;
    SV_V3Mutex m_mutex;
    SV_IntWrapper m_common_value_handle;
    function new(int sleep_iter, SV_V3Mutex mutex_ref, SV_IntWrapper common_value_handle_ref);
        super.new();
        m_sleep_iter = sleep_iter;
        m_mutex = mutex_ref;
        m_common_value_handle = common_value_handle_ref;
    endfunction
    task execute();
        SV_V3LockGuard lock;
        SV_V3LockGuard lock2;
        super.execute();
        repeat(m_sleep_iter) begin end
        lock = new(m_mutex);
        lock.acquire();
        m_common_value_handle.set(10);
        lock.do_release(); 
        repeat(m_sleep_iter + 10) begin end
        lock2 = new(m_mutex);
        lock2.acquire();
        `UASSERT(m_common_value_handle.get() == 10, $sformatf("selfTest: unexpected commonValue = %0d in firstJob", m_common_value_handle.get()));
        lock2.do_release(); 
    endtask
endclass
class SecondJobExecutor extends SV_V3Job;
    int m_sleep_iter;
    SV_V3Mutex m_mutex;
    SV_IntWrapper m_common_value_handle;
    function new(int sleep_iter, SV_V3Mutex mutex_ref, SV_IntWrapper common_value_handle_ref);
        super.new();
        m_sleep_iter = sleep_iter;
        m_mutex = mutex_ref;
        m_common_value_handle = common_value_handle_ref;
    endfunction
    task execute();
        SV_V3LockGuard lock;
        super.execute();
        m_mutex.lock();
        m_mutex.unlock();
        lock = new(m_mutex);
        lock.acquire();
        repeat(m_sleep_iter) begin end
        m_common_value_handle.set(1000);
        lock.do_release(); 
    endtask
endclass
class ThirdJobExecutor extends SV_V3Job;
    int m_sleep_iter;
    SV_V3Mutex m_mutex;
    SV_IntWrapper m_common_value_handle;
    function new(int sleep_iter, SV_V3Mutex mutex_ref, SV_IntWrapper common_value_handle_ref);
        super.new();
        m_sleep_iter = sleep_iter;
        m_mutex = mutex_ref;
        m_common_value_handle = common_value_handle_ref;
    endfunction
    task execute();
        SV_V3LockGuard lock;
        FirstJobExecutor f_job;
        SV_V3LockGuard lock_final;
        super.execute();
        begin
            lock = new(m_mutex);
            lock.acquire();
            repeat(m_sleep_iter) begin end
            lock.do_release(); 
        end
        f_job = new(m_sleep_iter, m_mutex, m_common_value_handle);
        f_job.execute();
        lock_final = new(m_mutex);
        lock_final.acquire();
        m_common_value_handle.set(100);
        lock_final.do_release(); 
    endtask
endclass
class ForthJobExecutor extends SV_V3Job;
    SV_IntWrapper m_result_handle;
    function new(SV_IntWrapper result_handle_ref);
        super.new();
        m_result_handle = result_handle_ref;
    endfunction
    task execute();
        super.execute();
        m_result_handle.set(1234);
    endtask
endclass
class InfiniteJob extends SV_V3Job;
    function new();
        super.new();
    endfunction
    task execute();
        super.execute();
        forever begin
        end
    endtask
endclass
module BasicThreadPoolTest (
    input bit start_test_m1,
    output int jobs_completed_sum
);
    SV_V3ThreadPool_Sim my_pool;
    SV_IntWrapper shared_counter_wrapper;
    IncrementJob job_inst;
    initial begin
        if (start_test_m1) begin
            my_pool = new(4);
            SV_V3Global::get_instance().set_threadPoolp(my_pool);
            shared_counter_wrapper = new(0);
            fork
                for (int i = 0; i < 10; i++) begin
                    job_inst = new(shared_counter_wrapper);
                    my_pool.enqueue(job_inst);
                end
                my_pool.wait_for_all_jobs();
                jobs_completed_sum = shared_counter_wrapper.get();
                `UASSERT(jobs_completed_sum == 10, $sformatf("BasicThreadPoolTest: Unexpected jobs_completed_sum value: %0d", jobs_completed_sum));
                my_pool.shutdown_pool();
            join_none
        end
    end
endmodule
module SingleThreadedPoolTest (
    input bit start_test_m2,
    output int result_val
);
    SV_V3ThreadPool_Sim single_pool;
    SV_IntWrapper result_val_wrapper;
    AddJob job_a;
    MultiplyJob job_b;
    function void callSelfTestMtDisabled();
    endfunction
    initial begin
        if (start_test_m2) begin
            single_pool = new(1);
            SV_V3Global::get_instance().set_threadPoolp(single_pool);
            result_val_wrapper = new(0);
            job_a = new(result_val_wrapper);
            job_b = new(result_val_wrapper);
            single_pool.enqueue(job_a);
            single_pool.enqueue(job_b);
            single_pool.wait_for_all_jobs();
            result_val = result_val_wrapper.get();
            `UASSERT(result_val == 15, $sformatf("SingleThreadedPoolTest: Unexpected result_val: %0d", result_val));
            callSelfTestMtDisabled();
        end
    end
endmodule
module SelfTestSimulation (
    input bit enable_self_test,
    output int final_common_value
);
    SV_V3Mutex commonMutex;
    SV_IntWrapper commonValueWrapper;
    SV_V3ThreadPool_Sim self_test_pool;
    SV_V3ThreadScope scope_block_var;
    SV_IntWrapper result_forth_wrapper_var;
    FirstJobExecutor  job_f1_100a, job_f1_100b, job_f1_200, job_f1_300;
    SecondJobExecutor job_s2_100a, job_s2_100b, job_s2_200;
    ThirdJobExecutor  job_t3_100a, job_t3_100b;
    ForthJobExecutor  job_forth;
    initial begin
        if (enable_self_test) begin
            self_test_pool = new(2);
            SV_V3Global::get_instance().set_threadPoolp(self_test_pool);
            commonMutex = new();
            commonValueWrapper = new(0);
            begin : scope_block1
                scope_block_var = new();
                scope_block_var.initial_wait_scope_jobs();
                job_f1_100a = new(100, commonMutex, commonValueWrapper);
                job_s2_100a = new(100, commonMutex, commonValueWrapper);
                job_f1_100b = new(100, commonMutex, commonValueWrapper);
                job_s2_100b = new(100, commonMutex, commonValueWrapper);
                job_s2_200 = new(200, commonMutex, commonValueWrapper);
                job_f1_200 = new(200, commonMutex, commonValueWrapper);
                job_f1_300 = new(300, commonMutex, commonValueWrapper);
                scope_block_var.enqueue(job_f1_100a);
                scope_block_var.enqueue(job_s2_100a);
                scope_block_var.enqueue(job_f1_100b);
                scope_block_var.enqueue(job_s2_100b);
                scope_block_var.enqueue(job_s2_200);
                scope_block_var.enqueue(job_f1_200);
                scope_block_var.enqueue(job_f1_300);
                scope_block_var.perform_wait_scope_jobs();
                `UASSERT(commonValueWrapper.get() == 1000 || commonValueWrapper.get() == 10, $sformatf("selfTest: unexpected common value = %0d after first block", commonValueWrapper.get()));
                job_t3_100a = new(100, commonMutex, commonValueWrapper);
                job_t3_100b = new(100, commonMutex, commonValueWrapper);
                scope_block_var.enqueue(job_t3_100a);
                scope_block_var.enqueue(job_t3_100b);
                scope_block_var.perform_wait_scope_jobs();
            end : scope_block1
            `UASSERT(commonValueWrapper.get() == 100, $sformatf("selfTest: unexpected common value = %0d after second block", commonValueWrapper.get()));
            begin : scope_block2
                scope_block_var = new();
                scope_block_var.initial_wait_scope_jobs();
                job_f1_100a = new(100, commonMutex, commonValueWrapper);
                scope_block_var.enqueue(job_f1_100a);
                scope_block_var.perform_wait_scope_jobs();
            end : scope_block2
            `UASSERT(commonValueWrapper.get() == 10, $sformatf("selfTest: unexpected common value = %0d after third block", commonValueWrapper.get()));
            begin : scope_block3
                result_forth_wrapper_var = new(0);
                scope_block_var = new();
                scope_block_var.initial_wait_scope_jobs();
                job_forth = new(result_forth_wrapper_var);
                scope_block_var.enqueue(job_forth);
                scope_block_var.perform_wait_scope_jobs();
                `UASSERT(result_forth_wrapper_var.get() == 1234, $sformatf("selfTest: unexpected job result = %0d", result_forth_wrapper_var.get()));
            end : scope_block3
            self_test_pool.shutdown_pool();
            final_common_value = commonValueWrapper.get();
        end
    end
endmodule
module ShutdownTest (
    input bit trigger_shutdown,
    output bit shutdown_complete
);
    SV_V3ThreadPool_Sim shutdown_pool;
    InfiniteJob inf_job;
    initial begin
        if (trigger_shutdown) begin
            shutdown_pool = new(2);
            SV_V3Global::get_instance().set_threadPoolp(shutdown_pool);
            shutdown_complete = 0;
            fork
                inf_job = new();
                shutdown_pool.enqueue(inf_job);
                shutdown_pool.shutdown_pool();
                shutdown_complete = 1;
            join_none
        end
    end
endmodule
